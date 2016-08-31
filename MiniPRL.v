(* A Coq port of MiniPRL [1]. While we make relatively heavy use of dependent
   types to keep track of bound variables, there aren't really any proofs. A
   longer term goal is to implement some of the ideas of Verified NuPRL [2].

   [1]: https://github.com/jozefg/miniprl
   [2]: http://www.nuprl.org/html/Nuprl2Coq/ *)
Require Fin Vector String.
Require Import List Arith.
Import ListNotations.

From StructTact Require Import StructTactics Assoc.

(* The stdlib notations for vector are broken so we roll our own. *sigh* *)
Arguments Vector.nil {_}.
Arguments Vector.cons {_} _ {_} _.

Delimit Scope vector_scope with vector.
Bind Scope vector_scope with Vector.t.

Notation "[ ]" := Vector.nil : vector_scope.
Notation "h :: t" := (Vector.cons h t) (at level 60, right associativity) : vector_scope.
Notation " [ x ] " := (x :: [])%vector : vector_scope.
Notation " [ x ; y ; .. ; z ] " := (x :: (y :: .. (z :: []) ..))%vector : vector_scope.

Open Scope vector_scope.

Set Implicit Arguments.

(* One kind of expression in our language will be a user-defined constant. Such
   constants are referred to by a guid.t, which is just a string name. *)
Module guid.
  Definition t := String.string.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y} := String.string_dec.
End guid.

(* Tactic for inverting equalities between dependent pairs where the first
   component has type nat. *)
Ltac inv_existT := repeat match goal with
| [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
  apply Eqdep_dec.inj_pair2_eq_dec in H; [| solve [auto using PeanoNat.Nat.eq_dec]]
end; subst.

Module expr.
  (* De Bruijn indices are *hard*, so to help ourselves out, we'll keep track of
     the number of free indices in the type. So a closed term will end up having
     type `expr.t 0`, while a term with one free variable would have type `expr.t
     1`.

     This is fairly easy to understand just by looking at the cases for
     variables, function application, and abstraction.

     * A variable is represented by an element of `Fin.t n` (which is a type
       with exactly `n` elements). So for example, in a closed term, since there
       are no elements of `Fin.t 0` (isomorphic to the empty type), one cannot
       have a variable at the top level, which makes sense.

     * Abstraction takes a body with one more free de Bruijn index and closes it
       off. So starting from a closed context (`expr.t 0`), going under a lambda
       gives us one free index to play with (`expr.t 1`). The identity function
       `\x.x` is thus represented by `Lam (Var Fin.F1)`, where in this case you
       can think of `Fin.F1` as naming the unique element of the type `Fin.t 1`.

     * Application takes two subterms with the same number of free variables.
       This makes sense, since it binds no variables.

     Other expression forms are similar to one or another of the above forms.
     Whenever a subterm binds variables, the type changes to reflect it.

     This is rather a lot of boilerplate-y work, but it really pays off in
     knowing that the binding structure of terms is being respected. If you've
     tried to implement a de Bruijn based representation without this help, you
     will have encountered many bugs due to forgotten lifting etc. Those become
     static errors with this representation!
   *)
  Inductive t : nat -> Type :=
  | Var : forall n, Fin.t n -> t n
  | Lam : forall n, t (S n) -> t n
  | App : forall n, t n -> t n -> t n
  | Pi : forall n, t n -> t (S n) -> t n

  | Pair : forall n, t n -> t n -> t n
  | Fst : forall n, t n -> t n
  | Snd : forall n, t n -> t n
  | Sig : forall n, t n -> t (S n) -> t n

  | tt : forall {n}, t n
  | Unit : forall {n}, t n

  | Eq : forall n, t n -> t n -> t n -> t n
  | Uni : forall (level : nat) {n}, t n

  | Cust : forall {n}, guid.t -> t n
  .

  (* The rest of this module defines some fundamental operations on the syntax,
     such as lifting and substitution. *)

  (* First up: lifting. `lift` will have the following signature:

         lift (c : nat) {n} (e : t n) : t (S n)

     It takes a term with `n` free variables and shifts them all up by one to
     make room for a new one. This is complicated by the fact that we don't want
     to mess up any bound variables in `e` by shifting them around. The
     parameter `c` keeps track of the number of *bound* variables in the
     context. If a variable is less than `c`, then it means it is bound by the
     context and should not be shifted. Users of this function will almost
     always want to pass 0 for `c`. *)

  (* Before defining lift, we define a helper function to examine a variable
     (represented by `f : Fin.t n`) and decide whether to shift it (if it is >=
     c) or leave it alone (< c). We could do this by converting `f` to a nat and
     then comparing against `c`, but it turns out to be more convenient to just
     directly examine `c` and `f` by recursion and do the right thing. *)
  Fixpoint lift_fin (c : nat) {n} (f : Fin.t n) : Fin.t (S n) :=
    match c with
    | 0 => Fin.FS f
    | S c' => match f with
             | Fin.F1 => Fin.F1
             | Fin.FS f => Fin.FS (lift_fin c' f)
             end
    end.

  (* Now we can define lift. The only hard part is remembering to increment `c`
     when descending under a binder. *)
  Fixpoint lift (c : nat) {n} (e : t n) : t (S n) :=
    match e with
    | Var f => Var (lift_fin c f)
    | Lam e => Lam (lift (S c) e)
    | App e1 e2 => App (lift c e1) (lift c e2)
    | Pi e1 e2 => Pi (lift c e1) (lift (S c) e2)
    | Pair e1 e2 => Pair (lift c e1) (lift c e2)
    | Fst e => Fst (lift c e)
    | Snd e => Snd (lift c e)
    | Sig e1 e2 => Sig (lift c e1) (lift (S c) e2)
    | tt => tt
    | Unit => Unit
    | Eq e1 e2 e3 => Eq (lift c e1) (lift c e2) (lift c e3)
    | Uni i => Uni i
    | Cust g => Cust g
    end.

  (* Next we define substitution. We go ahead and define multisubstitution
     because it actually turns out to be slightly simpler. (Instead of needing
     to check whether a variable is "equal" to a given nat, we just need to look
     up the variable's index in a vector.)

     Multisubstitution takes an expression `e` with `n` free variables and a map
     from the free variables of `e` to expressions with `n'` free variables and
     returns an expression with `n'` free variables. *)
  Fixpoint subst {n} (e : t n) {n'} : Vector.t (t n') n -> t n' :=
    let rec_bind {n} (e : t (S n)) {n'} (v : Vector.t (t n') n) :=
        subst e (Var Fin.F1 :: Vector.map (lift 0) v) in
    match e with
    | Var f => fun v => Vector.nth v f
    | Lam e => fun v => Lam (rec_bind e v)
    | App e1 e2 => fun v => App (subst e1 v) (subst e2 v)
    | Pi e1 e2 => fun v => Pi (subst e1 v) (rec_bind e2 v)
    | Pair e1 e2 => fun v => Pair (subst e1 v) (subst e2 v)
    | Fst e => fun v => Fst (subst e v)
    | Snd e => fun v => Snd (subst e v)
    | Sig e1 e2 => fun v => Sig (subst e1 v) (rec_bind e2 v)
    | tt => fun _ => tt
    | Unit => fun _ => Unit
    | Eq e1 e2 e3 => fun v => Eq (subst e1 v) (subst e2 v) (subst e3 v)
    | Uni i => fun _ => Uni i
    | Cust g => fun _ => Cust g
    end.

  (* To recover "normal" substitution of a single free variable, we need a way
     of saying "don't touch the rest of the variables". This is the purpose of
     `identity_subst`. It returns a map representing the identity function. *)
  Fixpoint identity_subst (n : nat) : Vector.t (t n) n :=
    match n with
    | 0 => []
    | S n => Var Fin.F1 :: Vector.map (lift 0) (identity_subst n)
    end.

  (* Recursion scheme for closed terms.
     Note that the vanilla scheme for terms requires the motive to generalize
     over the number of free variables, which is often inconvenient.
     This scheme let's the motive stay specific to closed terms, if one
     is willing to give up the ability to recurse under binders.

     Unfortunately this is rather verbose and boring. For each constructor,
     we need a hypothesis that transforms evidence of P on closed subterms to
     evidence for P on the parent term. So for example, function application
     gets two induction hypotheses, one for each sub term. But abstraction (lambda)
     gets no induction hypotheses because the subterm is not closed, and so we're
     not allowed to recurse. *)
  Section rec0.
    Variable P : t 0 -> Type.
    Hypothesis PLam : forall e, P (Lam e).
    Hypothesis PApp : forall e1 e2, P e1 -> P e2 -> P (App e1 e2).
    Hypothesis PPi : forall e1 e2, P e1 -> P (Pi e1 e2).
    Hypothesis PPair : forall e1 e2, P e1 -> P e2 -> P (Pair e1 e2).
    Hypothesis PFst : forall e, P e -> P (Fst e).
    Hypothesis PSnd : forall e, P e -> P (Snd e).
    Hypothesis PSig : forall e1 e2, P e1 -> P (Sig e1 e2).
    Hypothesis Ptt : P tt.
    Hypothesis Punit : P Unit.
    Hypothesis PEq : forall e1 e2 e3, P e1 -> P e2 -> P e3 -> P (Eq e1 e2 e3).
    Hypothesis PUni : forall i, P (Uni i).
    Hypothesis PCust : forall g, P (Cust g).


    Fixpoint rec0 (e : expr.t 0) : P e.
      refine match e with
             | Var f => _
             | @Lam n e => _
             | App e1 e2 => _
             | Pi e1 e2 => _
             | Pair e1 e2 => _
             | Fst e => _
             | Snd e => _
             | Sig e1 e2 => _
             | tt => _
             | Unit => _
             | Eq e1 e2 e3 => _
             | Uni i => _
             | Cust i => _
             end; destruct n; try exact (fun A x => x).
      - destruct f using Fin.case0.
      - apply PLam.
      - apply PApp; apply rec0.
      - apply PPi; apply rec0.
      - apply PPair; apply rec0.
      - apply PFst; apply rec0.
      - apply PSnd; apply rec0.
      - apply PSig; apply rec0.
      - apply Ptt.
      - apply Punit.
      - apply PEq; apply rec0.
      - apply PUni.
      - apply PCust.
    Defined.
  End rec0.

  (* A case analysis scheme for closed terms. Similar to `rec0` above, but no
     induction hypotheses (recursive calls) are generated at all.

     Implemented as a thin wrapper over `rec0` that ignores IHs.
   *)
  Definition case0 (P : t 0 -> Type)
             (PLam : forall e, P (Lam e))
             (PApp : forall e1 e2, P (App e1 e2))
             (PPi : forall e1 e2, P (Pi e1 e2))
             (PPair : forall e1 e2, P (Pair e1 e2))
             (PFst : forall e, P (Fst e))
             (PSnd : forall e, P (Snd e))
             (PSig : forall e1 e2, P (Sig e1 e2))
             (Ptt : P tt)
             (Punit : P Unit)
             (PEq : forall e1 e2 e3, P (Eq e1 e2 e3))
             (PUni : forall i, P (Uni i))
             (PCust : forall g, P (Cust g))
    : forall e, P e :=
    rec0 P
         PLam
         (fun e1 e2 _ _ => PApp e1 e2)
         (fun e1 e2 _ => PPi e1 e2)
         (fun e1 e2 _ _ => PPair e1 e2)
         (fun e _ => PFst e)
         (fun e _ => PSnd e)
         (fun e1 e2 _ => PSig e1 e2)
         Ptt
         Punit
         (fun e1 e2 e3 _ _ _ => PEq e1 e2 e3)
         PUni
         PCust
  .


  (* Equality decider. This should really be auto-generated but `decide equality`
     doesn't support dependent types :( *)
  Fixpoint eq_dec {n} (e1 : t n) : forall e2 : t n, {e1 = e2} + {e1 <> e2}.
    refine match e1 in t n0 return forall e2 : t n0, _ with
           | Var x          => fun e2 =>
             match e2 as e2' in t n0 return forall x : Fin.t n0, {Var x = e2'} + {Var x <> e2'} with
             | Var y => fun x =>
               match Fin.eq_dec x y with
               | left _ => left _
               | right _ => right _
               end
             | _ => fun x => right _
             end x
           | Lam e1         => fun e2 =>
             match e2 as e2' return forall e1, {Lam e1 = e2'} + {Lam e1 <> e2'} with
             | Lam e2 => fun e1 =>
               match eq_dec _ e1 e2 with
               | left _ => left _
               | right _ => right _
               end
             | _ => fun x => right _
             end e1
           | App e11 e12    => fun e2 =>
             match e2 as e2' return forall e11 e12, {App e11 e12 = e2'} + {App e11 e12 <> e2'} with
             | App e21 e22 => fun e11 e12 =>
               match eq_dec _ e11 e21 with
               | left _ =>
                 match eq_dec _ e12 e22 with
                 | left _ => left _
                 | right _ => right _
                 end
               | right _ => right _
               end
             | _ => fun _ _ => right _
             end e11 e12
           | Pi e11 e12     => fun e2 =>
             match e2 as e2' return forall e11 e12, {Pi e11 e12 = e2'} + {Pi e11 e12 <> e2'} with
             | Pi e21 e22 => fun e11 e12 =>
               match eq_dec _ e11 e21 with
               | left _ =>
                 match eq_dec _ e12 e22 with
                 | left _ => left _
                 | right _ => right _
                 end
               | right _ => right _
               end
             | _ => fun _ _ => right _
             end e11 e12
           | Pair e11 e12    => fun e2 =>
             match e2 as e2' return forall e11 e12, {Pair e11 e12 = e2'} + {Pair e11 e12 <> e2'} with
             | Pair e21 e22 => fun e11 e12 =>
               match eq_dec _ e11 e21 with
               | left _ =>
                 match eq_dec _ e12 e22 with
                 | left _ => left _
                 | right _ => right _
                 end
               | right _ => right _
               end
             | _ => fun _ _ => right _
             end e11 e12
           | Fst e1         => fun e2 =>
             match e2 as e2' return forall e1, {Fst e1 = e2'} + {Fst e1 <> e2'} with
             | Fst e2 => fun e1 =>
               match eq_dec _ e1 e2 with
               | left _ => left _
               | right _ => right _
               end
             | _ => fun _ => right _
             end e1
           | Snd e1         => fun e2 =>
             match e2 as e2' return forall e1, {Snd e1 = e2'} + {Snd e1 <> e2'} with
             | Snd e2 => fun e1 =>
               match eq_dec _ e1 e2 with
               | left _ => left _
               | right _ => right _
               end
             | _ => fun _ => right _
             end e1
           | Sig e11 e12     => fun e2 =>
             match e2 as e2' return forall e11 e12, {Sig e11 e12 = e2'} + {Sig e11 e12 <> e2'} with
             | Sig e21 e22 => fun e11 e12 =>
               match eq_dec _ e11 e21 with
               | left _ =>
                 match eq_dec _ e12 e22 with
                 | left _ => left _
                 | right _ => right _
                 end
               | right _ => right _
               end
             | _ => fun _ _ => right _
             end e11 e12
           | tt             => fun e2 =>
             match e2 as e2' return {tt = e2'} + {tt <> e2'} with
             | tt => left _
             | _ => right _
             end
           | Unit           => fun e2 => _
             match e2 as e2' return {Unit = e2'} + {Unit <> e2'} with
             | Unit => left _
             | _ => right _
             end
           | Eq e11 e12 e13 => fun e2 =>
             match e2 as e2' return forall e11 e12 e13, {Eq e11 e12 e13 = e2'} + {Eq e11 e12 e13 <> e2'} with
             | Eq e21 e22 e23 => fun e11 e12 e13 =>
               match eq_dec _ e11 e21 with
               | left _ =>
                 match eq_dec _ e12 e22 with
                 | left _ =>
                   match eq_dec _ e13 e23 with
                   | left _ => left _
                   | right _ => right _
                   end
                 | right _ => right _
                 end
               | right _ => right _
               end
             | _ => fun _ _ _ => right _
             end e11 e12 e13
           | Uni i          => fun e2 =>
             match e2 as e2' return {Uni i = e2'} + {Uni i <> e2'} with
             | Uni j =>
               match Nat.eq_dec i j with
               | left _ => left _
               | right _ => right _
               end
             | _ => right _
             end
           | Cust g1        => fun e2 =>
             match e2 as e2' return {Cust g1 = e2'} + {Cust g1 <> e2'} with
             | Cust g2 =>
               match guid.eq_dec g1 g2 with
               | left _ => left _
               | right _ => right _
               end
             | _ => right _
             end
           end; try congruence; try solve [intro H; invc H];
                try solve [intro H; invc H; inv_existT; congruence].
  Defined.
End expr.

Module context.
  (* A telescope binding n variables. Later types may refer to earlier bindings. *)
  Inductive t : nat -> Type :=
  | nil : t 0
  | cons : forall n (e : expr.t n) (C : t n), t (S n)
  .

  (* Looking up an element of the telescope lifts the answer so that it is well
     formed in the context of *all* bindings of the telescope. *)
  Fixpoint nth {n} (C : t n) : Fin.t n -> expr.t n.
    refine match C with
           | nil => fun f => _
           | cons e C => fun f => _
           end.
    - destruct f using Fin.case0.
    - apply (expr.lift 0).
      destruct f using Fin.caseS'.
      + exact e.
      + exact (nth _ C f).
  Defined.
End context.

Module goal.
  (* A sequent with n hypotheses. *)
  Record t (n : nat) : Type :=
    Make {
        context : context.t n;
        goal : expr.t n
    }.
End goal.

Module derivation.
  (* Derivations also bind variables, so they are indexed just like expressions are. *)
  Inductive t : nat -> Type :=
  | Pi_Eq n (D_A : t n) (D_B : t (S n)) : t n
  | Pi_Intro n (i : nat) (D_A : t n) (D_B : t (S n)) : t n
  | Pi_Elim n (H : Fin.t n) (a : expr.t n) (D_A : t n) (D_B : t (S n)) : t n

  | Lam_Eq n (i : nat) (D_A : t n) (D_B : t (S n)) : t n
  | Ap_Eq n (i : nat) (pi_ty : expr.t n) (D_fun D_arg D_cod : t n) : t n
  | Fun_Ext n (D_lhs D_rhs : t n) (D : t (S n)) : t n

  | Sig_Eq n (D_A : t n) (D_B : t (S n)) : t n
  | Sig_Intro n (i : nat) (a : expr.t n) (D_A D_B : t n) (D_eq : t (S n)) : t n
  | Sig_Elim n (H : Fin.t n) (D_C : t (S (S n))) : t n
  | Pair_Eq n (i : nat) (D_A D_B : t n) (D_ty : t (S n)) : t n
  | Fst_Eq n (sig_ty : expr.t n) (D : t n) : t n
  | Snd_Eq n (i : nat) (sig_ty : expr.t n) (D_a D_B : t n) : t n

  | Unit_Eq {n} : t n
  | tt_Eq {n} : t n
  | Unit_Intro {n} : t n

  | Eq_Eq n (D_ty D_lhs D_rhs : t n) : t n
  | Eq_Mem_Eq n : t n -> t n
  | Eq_Sym n : t n -> t n
  | Eq_Subst n (i : nat) (a : expr.t n) (D_ty : t (S n)) (D_eq D_body : t n) : t n

  | Uni_Eq {n} : t n
  | Cumulative n : t n -> t n

  | Witness n (w : expr.t n) : t n -> t n

  | Cut n (g : guid.t) : t (S n) -> t n

  | Var n (x : Fin.t n) : t n
  | Var_Eq {n} : t n
  .
End derivation.

Module extract.
  Fixpoint f {n} (D : derivation.t n) : expr.t n :=
    match D with
    | derivation.Pi_Eq D_A D_B => expr.tt
    | derivation.Pi_Intro i D_A D_B => expr.Lam (f D_B)
    | derivation.Pi_Elim x a D_A D_B =>
      expr.subst (f D_B) (expr.App (expr.Var x) a :: expr.identity_subst _)
    | derivation.Lam_Eq i D_A D_B => expr.tt
    | derivation.Ap_Eq i pi_ty D_fun D_arg D_cod => expr.tt
    | derivation.Fun_Ext D_lhs D_rhs H => expr.tt
    | derivation.Sig_Eq _ _ => expr.tt
    | derivation.Sig_Intro i a D_A D_B D_eq => (expr.Pair a (f D_B))
    | derivation.Sig_Elim H D_C =>
      expr.subst (f D_C) (expr.Snd (expr.Var H) :: expr.Fst (expr.Var H) :: expr.identity_subst _)
    | derivation.Pair_Eq _ _ _ _ => expr.tt
    | derivation.Fst_Eq _ _ => expr.tt
    | derivation.Snd_Eq _ _ _ _ => expr.tt
    | derivation.Unit_Eq => expr.tt
    | derivation.tt_Eq => expr.tt
    | derivation.Unit_Intro => expr.tt
    | derivation.Eq_Eq D_ty D_lhs D_rhs => expr.tt
    | derivation.Eq_Mem_Eq D => expr.tt
    | derivation.Eq_Sym D => expr.tt
    | derivation.Eq_Subst i a D_ty D_eq D_body => f D_body
    | derivation.Uni_Eq => expr.tt
    | derivation.Cumulative D => expr.tt
    | derivation.Witness w D => w
    | derivation.Cut g D =>
      expr.subst (f D) (expr.Cust g :: expr.identity_subst _)
    | derivation.Var x => expr.Var x
    | derivation.Var_Eq => expr.tt
    end.
End extract.

Module member.
  (* A proof-relevant proof that `a` is an element of the list `l`. This will be
     used as a dependently typed index into an `hlist.t` below. Analogizing to
     indexing a `Vector.t` with a `Fin.t`, `member.t` generalizes `Fin.t`. *)

  Local Open Scope list.
  Inductive t {A : Type} (a : A) : list A -> Type :=
  | Here : forall l, t a (a :: l)
  | There : forall b l, t a l -> t a (b :: l)
  .
  Arguments Here {_ _ _}.
  Arguments There {_ _ _ _} _.

  (* Useful case analysis schemes that preserve type information. *)
  Definition case_nil {A} {a : A} {P : Type} (m : t a []) : P :=
    match m with
    | Here => I
    | There m => I
    end.

  Definition case_cons {A} {a : A} {l} (P : forall a0, t a (a0 :: l) -> Type)
             (PHere : P _ Here)
             (PThere : forall a0 m, P a0 (There m))
             {a0} (m : t a (a0 :: l)) : P a0 m.
    revert P PHere PThere.
    refine match m with
           | Here => _
           | There m => _
           end; auto.
  Defined.
End member.


Module hlist.
  (* Heterogeneous lists. *)

  Local Open Scope list.
  Inductive t {A : Type} (B : A -> Type) : list A -> Type :=
  | nil : t B []
  | cons : forall a (b : B a) l (h : t B l), t B (a :: l).
  Arguments nil {_ _}.
  Arguments cons {_ _ _} _ {_} _.

  Delimit Scope hlist_scope with hlist.
  Bind Scope hlist_scope with hlist.t.

  Local Notation "[ ]" := nil : hlist_scope.
  Local Notation "h :: t" := (cons h t) (at level 60, right associativity) : hlist_scope.
  Local Notation " [ x ] " := (x :: [])%hlist : hlist_scope.
  Local Notation " [ x ; y ; .. ; z ] " := (x :: (y :: .. (z :: []) ..))%hlist : hlist_scope.

  Local Open Scope hlist_scope.

  (* Case analysis scheme for cons that preserves as much type information as
     possible. *)
  Section case_cons.
    Variable (A : Type) (B : A -> Type).
    Variable (a : A) (l : list A) (P : hlist.t B (a :: l) -> Type).

    Hypothesis H : forall b h, P (b :: h).

    Definition case_cons h : P h.
      revert P H.
      refine match h with
             | [] => I
             | b :: h => fun P H => H b h
             end.
    Defined.
  End case_cons.

  (* Index an hlist by giving a `member.t` as an index. *)
  Fixpoint get {A} {B : A -> Type} {l} (h : t B l) {a} {struct h} : member.t a l -> B a.
    refine match h with
           | [] => fun m => member.case_nil m
           | b :: h => fun m => _
           end.
    destruct a0, m using member.case_cons.
    - exact b.
    - exact (get _ _ _ h _ m).
  Defined.

  (* Now a bunch of utility functions on hlists... *)

  Fixpoint map A (B C : A -> Type) (f : forall a, B a -> C a) l (h : hlist.t B l) : hlist.t C l :=
    match h with
    | [] => []
    | b :: h => f _ b :: map _ f h
    end.

  Fixpoint of_vector S A (B : A -> Type) (f : S -> forall a, B a) l :
      Vector.t S (length l) -> hlist.t B l :=
    match l as l0 return Vector.t S (length l0) -> hlist.t B l0 with
    | []%list => fun v => []
    | (a :: l)%list => fun v => Vector.caseS' v _ (fun s v => f s a :: of_vector _ f _ v)
    end.

  Fixpoint to_list A (B : A -> Type) C (f : forall a, B a -> C) l (h : hlist.t B l) : list C :=
    match h with
    | [] => []%list
    | b :: h => (f _ b :: to_list f h)%list
    end.

  Fixpoint map_indices_dep A (B : A -> Type) C (D : C -> Type)
                             (f : forall a, B a -> C)
                             (g : forall a (b : B a), D (f a b))
                             l (h : hlist.t B l) :
      hlist.t D (to_list f h) :=
    match h as h0 return hlist.t D (to_list f h0) with
    | [] => []
    | b :: h => g _ b :: map_indices_dep _ f g h
    end.

  Fixpoint map2 A (B C D : A -> Type) (f : forall a, B a -> C a -> D a) l
           (bs : hlist.t B l) : hlist.t C l -> hlist.t D l :=
    match bs with
    | [] => fun _ => []
    | b :: bs => fun cs => case_cons _ (fun c cs => f _ b c :: map2 _ f bs cs) cs
    end.

  (* oh dear... *)
  Fixpoint map2_dep A (B : A -> Type) C (D : C -> Type) E (F : E -> Type) (G : A -> Type)
                      (f : forall a, B a -> C)
                      (g : forall a, B a -> E)
                      (h : forall a (b : B a), D (f a b) -> F (g a b) -> G a)
                      (l : list A) (bs : hlist.t B l) :
    hlist.t D (to_list f bs) -> hlist.t F (to_list g bs) -> hlist.t G l :=
    match bs as bs0 in hlist.t _ l0
    return hlist.t D (to_list f bs0) -> hlist.t F (to_list g bs0) -> hlist.t G l0
    with
    | [] => fun _ _ => []
    | @cons _ _ a b l bs => fun ds fs =>
      hlist.case_cons (fun _ => hlist.t G (a :: l)) (fun d0 ds =>
        (hlist.case_cons (fun _ => hlist.t G (a :: l)) (fun f0 fs =>
          h _ _ d0 f0 :: map2_dep _ f g h _ ds fs
        ) fs)
      ) ds
    end.

  Fixpoint app A (B : A -> Type) l1 (h1 : hlist.t B l1) l2 (h2 : hlist.t B l2) :
    hlist.t B (l1 ++ l2) :=
    match h1 in hlist.t _ l10 return hlist.t B (l10 ++ l2) with
    | [] => h2
    | b :: h1 => b :: app h1 h2
    end.

  Fixpoint concat A (B : A -> Type) l (h : hlist.t (hlist.t B) l) : hlist.t B (List.concat l) :=
    match h in hlist.t _ l0 return hlist.t B (List.concat l0) with
    | [] => []
    | bs :: h => app bs (concat h)
    end.

  Fixpoint unapp A (B : A -> Type) l1 l2 : hlist.t B (l1 ++ l2) -> hlist.t B l1 * hlist.t B l2 :=
    match l1 as l10 return hlist.t B (l10 ++ l2) -> hlist.t B l10 * hlist.t B l2 with
    | []%list => fun h => ([], h)
    | (a :: l1)%list => fun h =>
      case_cons _ (fun b h =>
        let (h1, h2) := unapp l1 l2 h
        in (b :: h1, h2)) h
    end.

  Fixpoint unconcat A (B : A -> Type) l : hlist.t B (List.concat l) -> hlist.t (hlist.t B) l :=
    match l with
    | []%list => fun _ => []
    | (a :: l)%list => fun h =>
      let '(h1, h2) := unapp a (List.concat l) h
      in h1 :: unconcat l h2
    end.


  Module notations.
    Delimit Scope hlist_scope with hlist.
    Bind Scope hlist_scope with hlist.t.

    Notation "[ ]" := nil : hlist_scope.
    Notation "h :: t" := (cons h t) (at level 60, right associativity) : hlist_scope.
    Notation " [ x ] " := (x :: [])%hlist : hlist_scope.
    Notation " [ x ; y ; .. ; z ] " := (x :: (y :: .. (z :: []) ..))%hlist : hlist_scope.

  End notations.
End hlist.
Import hlist.notations.


Module tactic_monad.
  (* This is just a straight port of MiniPRL's tactic monad. Made possible by
     the fact that all backtracking is explicit instead of using exceptions. *)

  Definition t (R A : Type) : Type := (A -> option R) -> option R.

  Definition ret {R A} (x : A) : t R A := fun k => k x.
  Definition bind {R A B} (m : t R A) (f : A -> t R B) : t R B :=
    fun k => m (fun a => f a k).

  Definition map {R A B} (f : A -> B) (m : t R A) : t R B :=
    fun k => m (fun a => k (f a)).

  Definition ap {R A B} (f : t R (A -> B)) (m : t R A) : t R B :=
    fun k => f (fun g => m (fun a => k (g a))).

  Fixpoint sequence {R A} (l : list (t R A)) : t R (list A) :=
    match l with
    | [] => ret []
    | x :: xs => bind x (fun a => map (List.cons a) (sequence xs))
    end%list.

  (* Here are two analogous operations: sequencing vectors and hlists. *)
  Fixpoint sequence_vector {R A} {n} (v : Vector.t (t R A) n) : t R (Vector.t A n) :=
    match v with
    | [] => ret []
    | x :: xs => bind x (fun a => map (Vector.cons a) (sequence_vector xs))
    end.

  Fixpoint sequence_hlist {R} {A} {B : A -> Type} {l} (h : hlist.t (fun a => t R (B a)) l) :
    t R (hlist.t B l) :=
    match h with
    | hlist.nil => ret hlist.nil
    | hlist.cons x xs => bind x (fun a => map (hlist.cons a) (sequence_hlist xs))
    end.

  Definition fail {R A} : t R A := fun _ => None.

  Fixpoint choose {R A} (l : list (unit -> t R A)) : t R A :=
    match l with
    | [] => fail
    | x :: xs => fun k => match x tt k with
                      | Some a => Some a
                      | None => choose xs k
                      end
    end%list.

  Definition run {A} (x : t A A) : option A := x (@Some _).

  Module notations.
  Notation "m >>= f" := (bind m f) (at level 51, right associativity) : tactic_monad.
  Notation "m1 >> m2" := (bind m1 (fun _ => m2)) (at level 51, right associativity) : tactic_monad.

  Notation "x <- m ;; f" := (bind m (fun x => f)) (at level 51, right associativity) : tactic_monad.
  End notations.

End tactic_monad.
Import tactic_monad.notations.

Module tactic_result.
  (* Because we are tracking binding in the type system, we are going to need to
     know that a tactic returns a well-scoped term. So `result.t` is
     parametrized by the number of hypotheses in the context.

     Then, we need to do something kind of complicated to allow the tactic to
     generate an arbitrary number of subgoals, each with an arbitrary context.
     This is achieved by adding `binding_structure` below, which describes the
     number of hypotheses in the context of each subgoal. The length of this
     list is the number of subgoals. The subgoals are given as an hlist over
     `binding_structure`. Similarly, the derivation transformer expects an hlist
     of subderivations and returns a well-scoped derivation in the parent
     context.

     I think it's fair to say that this is really complicated and probably worth
     skipping on a first reading. However, it means that we rule out entire
     classes of bugs since tactics are never exposed to ill-scoped goals or
     derivations or to a list of goals or derivations with the wrong length.
     This implies, for example, that the `MalformedEvidence` exception is never
     thrown in MiniPRL, assuming I have not accidently fixed bugs while
     porting. *)
  Record t (D G : nat -> Type) n : Type :=
    Make {
        binding_structure : list nat;
        evidence : hlist.t D binding_structure -> D n;
        goals : hlist.t G binding_structure
      }.
  Arguments Make {_ _} _ _ _ _.
End tactic_result.

Module Type TACTIC.
  Parameter derivation goal : nat -> Type.

  Definition result n := tactic_result.t derivation goal n.

  (* Okay, now this is kind of interesting. We've been carefully tracking
     binding in the type system, but we don't want users of the tactics to have
     to annotate them with the number of hypotheses in the contexts. So instead,
     we require tactics to be polymorphic in the number of hypotheses. If a
     tactics doesn't like what it sees, it's free to fail in the monad.

     I first tried indexing tactics by the number of hypotheses, but this makes
     it really hard to express the `split` and `next` combinators
     below. Experience shows that tactics really are parametric in the number of
     hypotheses, subject to a few constraints on any configuration data passed
     as arguments to the tactics, which of course must be well formed in
     whatever context they happen to run in. *)
  Definition t := forall R n, goal n -> tactic_monad.t R (result n).
End TACTIC.

Module tactic <: TACTIC.
  Definition derivation := derivation.t.
  Definition goal := goal.t.

  Definition result := tactic_result.t derivation goal.

  Definition t := forall R n, goal n -> tactic_monad.t R (result n).
End tactic.

Module refiner.
  Module result.
    (* The only interesting thing here is the binding structure. A proved result
       gives a closed derivation and extract. An incomplete result includes a
       binding structure (argument `l` to constructor `Incomplete` below), and
       an hlist of subgoals over that binding structure. *)
    Inductive t :=
    | Proved : derivation.t 0 -> (* extract: *) expr.t 0 -> t
    | Incomplete l : hlist.t goal.t l -> t
    | Failed : t
    .
  End result.

  Definition prove (thm : expr.t 0) (t : tactic.t) : result.t :=
    match tactic_monad.run (t _ _ (goal.Make context.nil thm)) with
    | Some (@tactic_result.Make _ _ _ l ev gs) =>
      match l as l0 return (hlist.t _ l0 -> _) -> hlist.t _ l0 -> _ with
      | [] => fun ev gs => let d := ev hlist.nil in result.Proved d (extract.f d)
      | _ => fun _ _ => result.Incomplete gs
      end%list ev gs
    | None => result.Failed
    end.
End refiner.

Module primitive_tactics (T : TACTIC).
  Definition id : T.t :=
    fun R n g => tactic_monad.ret (tactic_result.Make n [n]
                                  (fun h => hlist.get h member.Here)
                                  [g]).

  Definition choose (t1 t2 : T.t) : T.t :=
    fun R n g => tactic_monad.choose [fun u => t1 R n g; fun u => t2 R n g].

  Definition result_of_hlist l n (ev : hlist.t T.derivation l -> T.derivation n)
             (rs : hlist.t T.result l) : T.result n.
    refine (let new_binding_structure :=
                hlist.to_list (fun n r => tactic_result.binding_structure r) rs
            in _).

    refine (tactic_result.Make _ (List.concat new_binding_structure) _ _).
    - intros h. apply ev.
      refine (let chunks := hlist.unconcat _ h in _). clearbody chunks. clear h.
      refine (let ds := hlist.map_indices_dep
                          (fun p => hlist.t T.derivation (snd p) -> T.derivation (fst p))
                          (fun n r => (n, tactic_result.binding_structure r))
                          (fun n r => tactic_result.evidence r) rs
              in _).
      refine (hlist.map2_dep _ _ _ (fun n r c d => _) _ chunks ds).
      exact (d c).
    - refine (hlist.concat (hlist.map_indices_dep _ _ (fun n r => tactic_result.goals r) _)).
  Defined.

  Definition assume_sb {A B R} (x : {A} + {B}) : tactic_monad.t R A :=
    match x with
    | left a => tactic_monad.ret a
    | _ => tactic_monad.fail
    end.

  Definition assume_so {A B R} (x : A + {B}) : tactic_monad.t R A :=
    match x with
    | inleft a => tactic_monad.ret a
    | _ => tactic_monad.fail
    end.

  Local Open Scope tactic_monad.

  Definition split (t : T.t) (ts : list T.t) : T.t :=
    fun R n g =>
      r <- t R n g ;;
      let 'tactic_result.Make _ binding_structure evidence goals := r in
      pf <- assume_sb (Nat.eq_dec (length ts) (length binding_structure)) ;;
      rs <- tactic_monad.sequence_hlist
             (hlist.map2 _ (fun n (t : _ -> _) g => t g)
               (hlist.of_vector _ (fun s a => s R a) _
                  (Vector.cast (Vector.of_list ts) pf))
               goals) ;;
      tactic_monad.ret (result_of_hlist evidence rs).

  Definition next (t1 t2 : T.t) : T.t :=
    fun R n g =>
      r <- t1 R n g ;;
      let 'tactic_result.Make _ binding_structure evidence goals := r in
      rs <- tactic_monad.sequence_hlist (hlist.map _ (fun n g => t2 R n g) goals) ;;
      tactic_monad.ret (result_of_hlist evidence rs).
End primitive_tactics.

Module P := primitive_tactics tactic.

Module rules.
  (* We're finally ready for the rules. As discussed above, our typing
     discipline guarantees several invariants of the refiner, including
     well-scopedness. Indeed, a few de Bruijn bugs in MiniPRL's rules were found
     while porting :) (To be fair, de Bruijn bugs cause code to fail so hard
     that they likely could have been found by more traditional methods.)*)
  Import P.
  Local Open Scope tactic_monad.

  Definition nullary_derivation {R n} (d : derivation.t n) : tactic_monad.t R _ :=
    tactic_monad.ret (tactic_result.Make(G:=goal.t) _ [] (fun _ => d) []).

  Module unit.
    Definition Eq : tactic.t :=
      fun R n g =>
      match g with
      | goal.Make ctx (expr.Eq expr.Unit expr.Unit (expr.Uni _)) =>
        nullary_derivation derivation.Unit_Eq
      | _ => tactic_monad.fail
      end.

    Definition Intro : tactic.t :=
      fun R n g =>
      match g with
      | goal.Make ctx expr.Unit => nullary_derivation derivation.Unit_Intro
      | _ => tactic_monad.fail
      end.

    Definition TTEq : tactic.t :=
      fun R n g =>
      match g with
      | goal.Make ctx (expr.Eq expr.tt expr.tt expr.Unit) =>
        nullary_derivation derivation.tt_Eq
      | _ => tactic_monad.fail
      end.
  End unit.

  Module pi.
    Definition Eq : tactic.t.
      intros R n g.
      destruct g.
      revert context.
      refine match goal with
             | expr.Eq l r (expr.Uni i) => _
             | _ => fun _ => tactic_monad.fail
             end. clear goal n n1 t.
      revert r.
      refine match l with
             | expr.Pi A B => fun r => _
             | _ => fun _ _ => tactic_monad.fail
             end. clear l n0.
      revert A B.
      refine match r with
             | expr.Pi A' B' => fun A B ctx => _
             | _ => fun _ _ _ => tactic_monad.fail
             end. clear r n.
      rename n0 into n.
      refine (tactic_monad.ret (tactic_result.Make _ [n; S n]
            (fun h => derivation.Pi_Eq (hlist.get h member.Here)
                                    (hlist.get h (member.There member.Here)))
            [goal.Make ctx (expr.Eq A A' (expr.Uni i));
             goal.Make (context.cons A ctx) (expr.Eq B B' (expr.Uni i))])).
    Defined.

    Definition Intro (i : nat) : tactic.t.
      intros R n g.
      destruct g.
      revert context.
      refine match goal with
             | expr.Pi A B => _
             | _ => fun _ => tactic_monad.fail
             end. clear n goal.
      rename n0 into n.
      intros ctx.
      refine (tactic_monad.ret (tactic_result.Make _ [n; S n]
            (fun h => derivation.Pi_Intro i (hlist.get h member.Here)
                                         (hlist.get h (member.There member.Here)))
            [goal.Make ctx (expr.Eq A A (expr.Uni i));
             goal.Make (context.cons A ctx) B])).
    Defined.

    Definition Elim (H : nat) (e : sigT expr.t) : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      destruct e as [n' e].
      refine (pf <- assume_sb (Nat.eq_dec n n') ;; _).
      subst n'.
      refine (x <- assume_so (Fin.of_nat H n) ;; _).

      refine (match context.nth ctx x in expr.t n0
                    return context.t n0 -> expr.t n0 -> expr.t n0 -> Fin.t n0 ->
                           tactic_monad.t R (tactic.result n0)
              with
             | expr.Pi A B => fun ctx g e x => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end ctx g e x).
      clear ctx0 g0 e0 x0 n.
      rename n0 into n.

      refine (tactic_monad.ret (tactic_result.Make _ [n; S n]
            (fun h => derivation.Pi_Elim x e (hlist.get h member.Here)
                                          (hlist.get h (member.There member.Here)))
            [goal.Make ctx (expr.Eq e e A);
             goal.Make (context.cons (expr.subst B (e :: expr.identity_subst n)) ctx)
                       (expr.lift 0 g)])).
    Defined.

    Definition LamEq (i : nat) : tactic.t.
      intros R n g.
      destruct g.
      revert context.
      refine match goal with
             | expr.Eq l r t => _
             | _ => fun _ => tactic_monad.fail
             end. clear goal n.
      revert r t.
      refine match l with
             | expr.Lam b1 => fun r => _
             | _ => fun _ _ _ => tactic_monad.fail
             end. clear l n0.
      revert b1.
      refine match r with
             | expr.Lam b2 => fun b1 t => _
             | _ => fun _ _ _ => tactic_monad.fail
             end.  clear r n.
      revert b1 b2.
      refine match t with
             | expr.Pi A B => fun b1 b2 ctx => _
             | _ => fun _ _ _ => tactic_monad.fail
             end. clear t n0.
      refine (tactic_monad.ret (tactic_result.Make _ [n; S n]
            (fun h => derivation.Lam_Eq i (hlist.get h member.Here)
                                       (hlist.get h (member.There member.Here)))
            [goal.Make ctx (expr.Eq A A (expr.Uni i));
             goal.Make (context.cons A ctx)
                       (expr.Eq b1 b2 B)])).
    Defined.


    Definition ApEq (i : nat) (ty : sigT expr.t) : tactic.t.
      intros R n g.
      destruct g.
      destruct ty as [n' ty].
      refine (pf <- assume_sb (Nat.eq_dec n n') ;; _).
      subst n'.
      revert goal context.
      refine match ty with
             | expr.Pi A B => fun goal => _
             | _ => fun _ _ => tactic_monad.fail
             end. clear ty n.
      revert A B.
      refine match goal with
             | expr.Eq l r t => _
             | _ => fun _ _ _ => tactic_monad.fail
             end. clear goal. clear n0.
      revert r t.
      refine match l with
             | expr.App n1 m1 => fun r => _
             | _ => fun _ _ _ _ _ => tactic_monad.fail
             end. clear l n.
      revert n1 m1.
      refine match r with
             | expr.App n2 m2 => fun n1 m1 t A B ctx => _
             | _ => fun _ _ _ _ _ _ => tactic_monad.fail
             end. clear r n0.
      refine (tactic_monad.ret (tactic_result.Make _ [n; n; n]
            (fun h => derivation.Ap_Eq i (expr.Pi A B)
                                    (hlist.get h member.Here)
                                    (hlist.get h (member.There member.Here))
                                    (hlist.get h (member.There (member.There member.Here))))
            [goal.Make ctx (expr.Eq n1 n2 (expr.Pi A B));
             goal.Make ctx (expr.Eq m1 m2 A);
             goal.Make ctx (expr.Eq (expr.subst B (n1 :: expr.identity_subst n))
                                    t
                                    (expr.Uni i))])).
    Defined.

    Definition FunExt : tactic.t.
      intros R n g.
      destruct g.
      revert context.
      refine match goal with
             | expr.Eq l r t => _
             | _ => fun _ => tactic_monad.fail
             end. clear goal n.
      revert l r.
      refine match t with
             | expr.Pi A B => fun l r ctx => _
             | _ => fun _ _ _ => tactic_monad.fail
             end.
      refine (tactic_monad.ret (tactic_result.Make _ [n; n; S n]
            (fun h => derivation.Fun_Ext (hlist.get h member.Here)
                                      (hlist.get h (member.There member.Here))
                                      (hlist.get h (member.There (member.There member.Here))))
            [goal.Make ctx (expr.Eq l l (expr.Pi A B));
             goal.Make ctx (expr.Eq r r (expr.Pi A B));
             goal.Make (context.cons A ctx)
                       (expr.Eq (expr.App (expr.lift 0 l) (expr.Var Fin.F1))
                                (expr.App (expr.lift 0 r) (expr.Var Fin.F1))
                                B)])).
    Defined.
  End pi.

  Module uni.
    Definition Eq : tactic.t.
      intros R n g.
      destruct g.
      revert context.
      refine match goal with
             | expr.Eq (expr.Uni i) (expr.Uni j) (expr.Uni k) => fun ctx => _
             | _ => fun _ => tactic_monad.fail
             end.
      refine (_ <- assume_sb (Nat.eq_dec i j) ;; _).
      refine (_ <- assume_sb (Nat.eq_dec (S i) k) ;; _).
      exact (nullary_derivation derivation.Uni_Eq).
    Defined.

    Definition Cumulative : tactic.t.
      intros R n g.
      destruct g.
      revert context.
      refine match goal with
             | expr.Eq A B (expr.Uni (S i)) => fun ctx => _
             | _ => fun _ => tactic_monad.fail
             end. clear goal n t n1 n2.
      rename n0 into n.
      refine (tactic_monad.ret (tactic_result.Make _ [n]
            (fun h => derivation.Cumulative (hlist.get h member.Here))
            [goal.Make ctx (expr.Eq A B (expr.Uni i))])).
    Defined.
  End uni.

  Module general.
    Definition Hyp (H : nat) : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      refine (x <- assume_so (Fin.of_nat H n) ;; _).
      refine (_ <- assume_sb (expr.eq_dec g (context.nth ctx x)) ;; _).
      exact (nullary_derivation (derivation.Var x)).
    Defined.

    Definition HypEq : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      revert ctx.
      refine match g with
             | expr.Eq l r t => _
             | _ => fun _ => tactic_monad.fail
             end. clear g n.
      revert r t.
      refine match l with
             | expr.Var x1 => fun r => _
             | _ => fun _ _ _ => tactic_monad.fail
             end. clear l n0.
      revert x1.
      refine match r with
             | expr.Var x2 => fun x1 t ctx => _
             | _ => fun _ _ _ => tactic_monad.fail
             end.  clear r n.
      refine (_ <- assume_sb (Fin.eq_dec x1 x2) ;; _).
      refine (_ <- assume_sb (expr.eq_dec t (context.nth ctx x1)) ;; _).
      exact (nullary_derivation derivation.Var_Eq).
    Defined.
  End general.

  Module eq.
    Definition Eq : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      revert ctx.
      refine match g with
             | expr.Eq l r (expr.Uni i) => _
             | _ => fun _ => tactic_monad.fail
             end. clear g n n1 t.
      revert r.
      refine match l with
             | expr.Eq m1 n1 A1 => fun r => _
             | _ => fun _ _ => tactic_monad.fail
             end. clear l n0.
      revert m1 n1 A1.
      refine match r with
             | expr.Eq m2 n2 A2 => fun m1 n1 A1 ctx => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear r n.
      rename n0 into n.
      refine (tactic_monad.ret (tactic_result.Make _ [n; n; n]
            (fun h => derivation.Eq_Eq (hlist.get h member.Here)
                                    (hlist.get h (member.There member.Here))
                                    (hlist.get h (member.There (member.There member.Here))))
            [goal.Make ctx (expr.Eq A1 A2 (expr.Uni i));
             goal.Make ctx (expr.Eq m1 m2 A1);
             goal.Make ctx (expr.Eq n1 n2 A1)])).
    Defined.
  End eq.

  Module sig.
    Definition Eq : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      revert ctx.
      refine match g with
             | expr.Eq l r (expr.Uni i) => _
             | _ => fun _ => tactic_monad.fail
             end. clear g n n1 t.
      revert r.
      refine match l with
             | expr.Sig A B => fun r => _
             | _ => fun _ _ => tactic_monad.fail
             end. clear l n0.
      revert A B.
      refine match r with
             | expr.Sig A' B' => fun A B ctx => _
             | _ => fun _ _ _ => tactic_monad.fail
             end. clear r n.
      rename n0 into n.
      refine (tactic_monad.ret (tactic_result.Make _ [n; S n]
            (fun h => derivation.Sig_Eq (hlist.get h member.Here)
                                     (hlist.get h (member.There member.Here)))
            [goal.Make ctx (expr.Eq A A' (expr.Uni i));
             goal.Make (context.cons A ctx) (expr.Eq B B' (expr.Uni i))])).
    Defined.

    Definition Intro (i : nat) (e : {n : nat & expr.t n}) : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      destruct e as [n' e].
      refine (pf <- assume_sb (Nat.eq_dec n n') ;; _).
      subst n'.
      revert e ctx.
      refine match g with
             | expr.Sig A B => fun a ctx => _
             | _ => fun _ _ => tactic_monad.fail
             end. clear g n.
      rename n0 into n.
      refine (tactic_monad.ret (tactic_result.Make _ [n; n; S n]
            (fun h => derivation.Sig_Intro i a
                                        (hlist.get h member.Here)
                                        (hlist.get h (member.There member.Here))
                                        (hlist.get h (member.There (member.There member.Here))))
            [goal.Make ctx (expr.Eq a a A);
             goal.Make ctx (expr.subst B (a :: expr.identity_subst n));
             goal.Make (context.cons A ctx) (expr.Eq B B (expr.Uni i))])).
    Defined.

    Definition Elim (H : nat) : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      refine (x <- assume_so (Fin.of_nat H n) ;; _).

      refine (match context.nth ctx x in expr.t n0
                    return context.t n0 -> expr.t n0 -> Fin.t n0 ->
                           tactic_monad.t R (tactic.result n0)
              with
             | expr.Sig A B => fun ctx g x => _
             | _ => fun _ _ _ => tactic_monad.fail
             end ctx g x).
      clear ctx0 g0 x0 n.
      rename n0 into n.
      refine (tactic_monad.ret (tactic_result.Make _ [S (S n)]
            (fun h => derivation.Sig_Elim x
                                       (hlist.get h member.Here))
            [goal.Make (context.cons B (context.cons A ctx)) (expr.lift 0 (expr.lift 0 g))])).
    Defined.

    Definition PairEq (i : nat) : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      revert ctx.
      refine match g with
             | expr.Eq l r t => _
             | _ => fun _ => tactic_monad.fail
             end. clear g n.
      revert r t.
      refine match l with
             | expr.Pair a b => fun r => _
             | _ => fun _ _ _ => tactic_monad.fail
             end. clear l n0.
      revert a b.
      refine match r with
             | expr.Pair a' b' => fun a b t => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear r n.
      revert a b a' b'.
      refine match t with
             | expr.Sig A B => fun a b a' b' ctx => _
             | _ => fun _ _ _ _ _ => tactic_monad.fail
             end. clear t n0.
      refine (tactic_monad.ret (tactic_result.Make _ [n; n; S n]
            (fun h => derivation.Pair_Eq i
                                       (hlist.get h member.Here)
                                       (hlist.get h (member.There member.Here))
                                       (hlist.get h (member.There (member.There member.Here))))
            [goal.Make ctx (expr.Eq a a' A);
             goal.Make ctx (expr.Eq b b' (expr.subst B (a :: expr.identity_subst n)));
             goal.Make (context.cons A ctx) (expr.Eq B B (expr.Uni i))])).
    Defined.


    Definition FstEq (ty : {n : nat & expr.t n}) : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      destruct ty as [n' ty].
      refine (pf <- assume_sb (Nat.eq_dec n n') ;; _).
      subst n'.
      revert ty ctx.
      refine match g with
             | expr.Eq l r t => _
             | _ => fun _ _ => tactic_monad.fail
             end. clear g n.
      revert r t.
      refine match l with
             | expr.Fst m1 => fun r => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear l n0.
      revert m1.
      refine match r with
             | expr.Fst m2 => fun m1 t ty ctx => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear r n.
      revert m1 m2 t ctx.
      refine match ty with
             | expr.Sig A B => fun m1 m2 t ctx => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear n0 ty.
      refine (_ <- assume_sb (expr.eq_dec t A) ;; _).
      refine (tactic_monad.ret (tactic_result.Make _ [n]
            (fun h => derivation.Fst_Eq (expr.Sig A B) (hlist.get h member.Here))
            [goal.Make ctx (expr.Eq m1 m2 (expr.Sig A B))])).
    Defined.

    Definition SndEq (i : nat) (ty : {n : nat & expr.t n}) : tactic.t.
      intros R n g.
      destruct g as [ctx g].
      destruct ty as [n' ty].
      refine (pf <- assume_sb (Nat.eq_dec n n') ;; _).
      subst n'.
      revert ty ctx.
      refine match g with
             | expr.Eq l r B' => _
             | _ => fun _ _ => tactic_monad.fail
             end. clear g n.
      revert r B'.
      refine match l with
             | expr.Snd m1 => fun r => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear l n0.
      revert m1.
      refine match r with
             | expr.Snd m2 => fun m1 B' ty ctx => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear r n.
      revert m1 m2 B' ctx.
      refine match ty with
             | expr.Sig A B => fun m1 m2 B' ctx => _
             | _ => fun _ _ _ _ => tactic_monad.fail
             end. clear n0 ty.
      refine (tactic_monad.ret (tactic_result.Make _ [n; n]
            (fun h => derivation.Snd_Eq i (expr.Sig A B)
                                     (hlist.get h member.Here)
                                     (hlist.get h (member.There member.Here)))
            [goal.Make ctx (expr.Eq m1 m2 (expr.Sig A B));
             goal.Make ctx (expr.Eq (expr.subst B (expr.Fst m1 :: expr.identity_subst _))
                                    B'
                                    (expr.Uni i))])).
    Defined.
  End sig.
End rules.
Import rules.

(* We can use our rules to prove stuff! *)
Eval compute in refiner.prove (expr.Eq expr.Unit expr.Unit (expr.Uni 0)) rules.unit.Eq.
Eval compute in refiner.prove expr.Unit rules.unit.Intro.
Eval compute in refiner.prove (expr.Eq expr.tt expr.tt expr.Unit) rules.unit.TTEq.

Module ast.
  (* Okay so it turns out that writing de Bruijn indices by hand is basically
     impossible. An AST allows writing terms using string names. ASTs can be
     converted to expressions by a partial operation that fails if things aren't
     well-scoped. *)
  Inductive t : Type :=
  | Var : String.string -> t
  | Lam : String.string -> t -> t
  | App : t -> t -> t
  | Pi : String.string -> t -> t -> t

  | Pair : t -> t -> t
  | Fst : t -> t
  | Snd : t -> t
  | Sig : String.string -> t -> t -> t

  | tt : t
  | Unit : t

  | Eq : t -> t -> t -> t
  | Uni (level : nat) : t

  | Cust : guid.t -> t
  .

  (* Helper function to find the first occurence of a particular value in a vector. *)
  Fixpoint v_index_of {A} (A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
           (a : A)
           {n} (v : Vector.t A n) : option (Fin.t n) :=
    match v with
    | [] => None
    | a' :: v => if A_eq_dec a a'
                then Some Fin.F1
                else match v_index_of A_eq_dec a v with
                     | None => None
                     | Some i => Some (Fin.FS i)
                     end
    end.

  Fixpoint to_expr' {n} (v : Vector.t String.string n) (a : t) : option (expr.t n) :=
    match a with
    | Var s =>
      match v_index_of String.string_dec s v with
      | Some i => Some (expr.Var i)
      | None => None
      end
    | Lam s a =>
      match to_expr' (s :: v) a with None => None
      | Some a => Some (expr.Lam a)
      end
    | App a1 a2 =>
      match to_expr' v a1 with None => None
      | Some a1 =>
      match to_expr' v a2 with None => None
      | Some a2 => Some (expr.App a1 a2)
      end end
    | Pi s a1 a2 =>
      match to_expr' v a1 with None => None
      | Some a1 =>
      match to_expr' (s :: v) a2 with None => None
      | Some a2 => Some (expr.Pi a1 a2)
      end end
    | Pair a1 a2 =>
      match to_expr' v a1 with None => None
      | Some a1 =>
      match to_expr' v a2 with None => None
      | Some a2 => Some (expr.Pair a1 a2)
      end end
    | Fst a =>
      match to_expr' v a with None => None
      | Some a => Some (expr.Fst a)
      end
    | Snd a =>
      match to_expr' v a with None => None
      | Some a => Some (expr.Snd a)
      end
    | Sig s a1 a2 =>
      match to_expr' v a1 with None => None
      | Some a1 =>
      match to_expr' (s :: v) a2 with None => None
      | Some a2 => Some (expr.Sig a1 a2)
      end end
    | tt => Some expr.tt
    | Unit => Some expr.Unit
    | Eq a1 a2 a3 =>
      match to_expr' v a1 with None => None
      | Some a1 =>
      match to_expr' v a2 with None => None
      | Some a2 =>
      match to_expr' v a3 with None => None
      | Some a3 => Some (expr.Eq a1 a2 a3)
      end end end
    | Uni i => Some (expr.Uni i)
    | Cust g => Some (expr.Cust g)
    end.

  Fixpoint to_expr (a : t) : option (expr.t 0) :=
    to_expr' [] a.

End ast.

Open Scope string_scope.

(* Writing Var all the time gets tiresome... *)
Coercion ast.Var : String.string >-> ast.t.

(* Here's an actually interesting theorem: function extensionality. Much *much*
   nicer to write this as an ast than as an expr! *)
Definition ast_funext : ast.t :=
  ast.Pi "A" (ast.Uni 0)
    (ast.Pi "B" (ast.Uni 0)
    (ast.Pi "f" (ast.Pi "_" "A" "B")
    (ast.Pi "g" (ast.Pi "_" "A" "B")
    (ast.Pi "_" (ast.Pi "x" "A" (ast.Eq (ast.App "f" "x") (ast.App "g" "x") "B"))
        (ast.Eq "f" "g" (ast.Pi "_" "A" "B")))))).

(* We can take a look at the resulting expr. *)
Eval compute in ast.to_expr (ast_funext).
(* Gross! *)

(* Since converting an ast to an expr is a partial operation, it cannot be used
   directly in Gallina to produce expressions. But we can wrap it in a tactic
   that will bail out during elaboration if parsing fails.

   Given an ast, `parse` tries to produce a *closed* expression. *)
Ltac parse e :=
  let e := eval compute in (ast.to_expr e)
  in match e with
     | Some ?x => exact x
     end.

(* When working in the refiner, we'll want to parse open terms in the context of
   the current goal. `parse'` takes the context as an extra argument to
   facilitate this. *)
Ltac parse' v e :=
  let e := eval compute in (ast.to_expr' v e)
  in match e with
     | Some ?x => exact x
     end.

(* We can use `parse` to conveniently define the expr for function
   extensionality without copy-pasting. *)
Definition funext : expr.t 0 := ltac:(parse ast_funext).

(* A few simple notations for the tactics. *)
Notation "t ;; l" := (P.split t l) (at level 51, right associativity).
Notation "t1 ;;; t2" := (P.next t1 t2) (at level 51, right associativity).

(* Let's prove function extensionality! *)
Eval cbv in refiner.prove funext
                (pi.Intro 1 ;; [uni.Eq;
                 pi.Intro 1 ;; [uni.Eq;
                 pi.Intro 0 ;; [pi.Eq ;; [general.HypEq; general.HypEq];
                 pi.Intro 0 ;; [pi.Eq ;; [general.HypEq; general.HypEq];
                 pi.Intro 0 ;; [pi.Eq ;; [general.HypEq;
                                    eq.Eq ;; [general.HypEq;
                        pi.ApEq 0
                           (existT _ _ ltac:(parse' ["x"; "g"; "f"; "B"; "A"]
                                                    (ast.Pi "_" "A" "B"))) ;;;
                           general.HypEq;
                        pi.ApEq 0
                           (existT _ _ ltac:(parse' ["x"; "g"; "f"; "B"; "A"]
                                                    (ast.Pi "_" "A" "B"))) ;;;
                           general.HypEq]];
                 pi.FunExt ;; [general.HypEq; general.HypEq;
                        pi.Elim 1
                          (existT _ _ ltac:(parse' ["x"; "H"; "g"; "f"; "B"; "A"] "x")) ;;
                          [ general.HypEq; general.Hyp 0 ]]]]]]]).

Definition ast_proj1 : ast.t :=
   ast.Pi "A" (ast.Uni 0)
  (ast.Pi "B" (ast.Pi "_" "A" (ast.Uni 0))
  (ast.Pi "_" (ast.Sig "x" "A" (ast.App "B" "x"))
          "A")).

Definition proj1 : expr.t 0 := ltac:(parse ast_proj1).

Eval cbv in refiner.prove proj1
  (pi.Intro 1;; [uni.Eq;
   pi.Intro 1;; [pi.Eq;; [uni.Cumulative;;; general.HypEq; uni.Eq];
   pi.Intro 0;; [sig.Eq;; [general.HypEq;
       pi.ApEq 1
         (existT _ _ ltac:(parse' ["x"; "B"; "A"] (ast.Pi "y" "A" (ast.Uni 0))));;
       [general.HypEq; general.HypEq; uni.Eq]];
   sig.Elim 0;; [general.Hyp 1]]]]).


Definition ast_snd_eq : ast.t :=
  ast.Eq (ast.Snd (ast.Pair ast.tt ast.tt))
         (ast.Snd (ast.Pair ast.tt ast.tt))
         ast.Unit.

Definition snd_eq : expr.t 0 := ltac:(parse ast_snd_eq).

Eval cbv in refiner.prove snd_eq
   (sig.SndEq 0 (existT _ _ ltac:(parse (ast.Sig "_" ast.Unit ast.Unit))) ;;
     [sig.PairEq 0 ;; [unit.TTEq; unit.TTEq; unit.Eq];
      unit.Eq]).

(* End of main development. *)





(* Eventually we will support user-defined constants. For now, this is unused. *)
Module configuration.
  Module entry.
    Record t :=
      Make {
          type : expr.t 0;
          extract : expr.t 0
        }.
  End entry.

  Definition t := list (guid.t * entry.t).

  Definition empty : t := []%list.

  Definition insert (name : guid.t) (type : expr.t 0) (extract : expr.t 0) (C : t) : t :=
    assoc_set guid.eq_dec C name (entry.Make type extract).

  Definition type_of (name : guid.t) (C : t) : option (expr.t 0) :=
    option_map entry.type (assoc guid.eq_dec C name).

  Definition extract_of (name : guid.t) (C : t) : option (expr.t 0) :=
    option_map entry.extract (assoc guid.eq_dec C name).
End configuration.


(* Eventually we should give meaning to the proof theory in terms of the
   underlying computation system. Then we should be able to show that the
   rules above are sound. *)

Module value.
  Inductive t : expr.t 0 -> Prop :=
  | Lam : forall e, t (expr.Lam e)
  | Pi : forall e1 e2, t (expr.Pi e1 e2)
  | tt : t expr.tt
  | Unit : t expr.Unit
  | Eq : forall e1 e2 e3, t (expr.Eq e1 e2 e3)
  | Uni : forall i, t (expr.Uni i)
  | Cust : forall g, t (expr.Cust g)
  .
  Hint Constructors t.
End value.

Module step.
  Module result.
    Inductive t :=
    | Step : expr.t 0 -> t
    | Value : t
    | Stuck : t
    .
  End result.

  Inductive t : expr.t 0 -> expr.t 0 -> Prop :=
  | Beta : forall e1 e2, t (expr.App (expr.Lam e1) e2) (expr.subst e1 [e2])
  | AppL : forall e1 e1' e2, t e1 e1' -> t (expr.App e1 e2) (expr.App e1' e2)
  .
  Hint Constructors t.

  Lemma det : forall e e1 e2, t e e1 -> t e e2 -> e1 = e2.
  Proof.
    intros.
    generalize dependent e2.
    induction H; intros.
    - invc H0.
      + apply Eqdep_dec.inj_pair2_eq_dec in H1; auto using PeanoNat.Nat.eq_dec.
        apply Eqdep_dec.inj_pair2_eq_dec in H2; auto using PeanoNat.Nat.eq_dec.
        subst.
        auto.
      + apply Eqdep_dec.inj_pair2_eq_dec in H; auto using PeanoNat.Nat.eq_dec.
        subst.
        solve_by_inversion.
    - invc H0.
      + apply Eqdep_dec.inj_pair2_eq_dec in H2; auto using PeanoNat.Nat.eq_dec.
        subst.
        solve_by_inversion.
      + apply Eqdep_dec.inj_pair2_eq_dec in H1; auto using PeanoNat.Nat.eq_dec.
        apply Eqdep_dec.inj_pair2_eq_dec in H3; auto using PeanoNat.Nat.eq_dec.
        subst.
        f_equal; auto.
  Qed.

  Definition f (e : expr.t 0) : result.t :=
    expr.rec0
      _
      (* Lam *) (fun _ => result.Value)
      (* App *) (fun e1 e2 IHe1 _ =>
                   match IHe1 with
                   | result.Step e1' => result.Step (expr.App e1' e2)
                   | result.Value => expr.case0
                                      _
                                      (* Lam *)(fun e1 => result.Step (expr.subst e1 [e2]))
                                      (* App *) (fun _ _ => result.Stuck)
                                      (* Pi *) (fun _ _ => result.Stuck)
                                      (* tt *) result.Stuck
                                      (* Unit *) result.Stuck
                                      (* Eq *) (fun _ _ _ => result.Stuck)
                                      (* Uni *) (fun i => result.Stuck)
                                      (* Cust *) (fun _ => result.Stuck)
                                      e1
                   | result.Stuck => result.Stuck
                   end)
      (* Pi *) (fun _ _ _ => result.Value)
      (* tt *) result.Value
      (* unit *) result.Value
      (* Eq *) (fun _ _ _ _ _ _ => result.Value)
      (* Uni *) (fun i => result.Value)
      (* Cust *) (fun _ => result.Value)
      e
  .

  Lemma f_t :
    forall e, match f e with
         | result.Step e' => t e e'
         | result.Value => value.t e
         | result.Stuck => (forall e', ~ t e e') /\ ~ value.t e
         end.
  Proof.
    induction e using expr.rec0; simpl; auto.
    - destruct (f e1).
      + auto.
      + invcs IHe1; intuition; invc H; inv_existT; try solve_by_inversion.
      + intuition; invc H1; inv_existT; eauto.
  Qed.
End step.

Module star.
  Definition t : expr.t 0 -> expr.t 0 -> Prop := Relation_Operators.clos_refl_trans_1n _ step.t.
End star.

Module eval.
  Definition t (e : expr.t 0) (v : expr.t 0) : Prop :=
    star.t e v /\ value.t v.
End eval.
