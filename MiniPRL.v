(* A Coq port of MiniPRL [1].
   A longer term goal is to implement some of the ideas of Verified NuPRL [2].

   [1]: https://github.com/jozefg/miniprl
   [2]: http://www.nuprl.org/html/Nuprl2Coq/ *)
Require String.
Require Import List Arith Bool Omega.
Import ListNotations.


From StructTact Require Import StructTactics Assoc BoolUtil.

Set Implicit Arguments.

(* One kind of expression in our language will be a user-defined constant. Such
   constants are referred to by a guid.t, which is just a string name. *)
Module guid.
  Definition t := String.string.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y} := String.string_dec.
End guid.

Module expr.
  Inductive t : Type :=
  | Var : nat -> t
  | Lam : t -> t
  | App : t -> t -> t
  | Pi : t -> t -> t

  | Pair : t -> t -> t
  | Fst : t -> t
  | Snd : t -> t
  | Sig : t -> t -> t

  | tt : t
  | Unit : t

  | Eq : t -> t -> t -> t
  | Uni (level : nat) : t

  | Cust : guid.t -> t
  .

  Module exports.
    Coercion Var : nat >-> t.
    Coercion App : expr.t >-> Funclass.
    Coercion Cust : guid.t >-> t.

    Notation Fst := Fst.
    Notation Snd := Snd.
    Notation tt := tt.
    Notation Unit := Unit.
    Notation Uni := Uni.
  End exports.

  Module notations.
    Bind Scope expr_scope with expr.t.
    Delimit Scope expr_scope with expr.


    Notation "'\' e" := (expr.Lam e) (at level 50) : expr_scope.
    Notation "A -> B" := (expr.Pi A B) : expr_scope.

    Notation "( x , y , .. , z )" := (expr.Pair .. (expr.Pair x y) .. z) : expr_scope.
    Notation "A * B" := (expr.Sig A B) : expr_scope.
    Notation "A = B 'in' C" := (expr.Eq A B C) (at level 50) : expr_scope.

    Local Open Scope expr.
    Import exports.

    Check (\ 0).
    Check (\ 0) (\ 0).
    Check (\ 0) -> (\ 0).
    Check (0, 0).
    Check (\ 0) * (\ 0).
    Check (\ 0) = (\ 0) in Unit.
  End notations.

  (* The rest of this module defines some fundamental operations on the syntax,
     such as lifting and substitution. *)
  Fixpoint lift (c d : nat) (e : t) : t :=
    match e with
    | Var n => if n <? c then Var n else Var (n + d)
    | Lam e => Lam (lift (S c) d e)
    | App e1 e2 => App (lift c d e1) (lift c d e2)
    | Pi e1 e2 => Pi (lift c d e1) (lift (S c) d e2)
    | Pair e1 e2 => Pair (lift c d e1) (lift c d e2)
    | Fst e => Fst (lift c d e)
    | Snd e => Snd (lift c d e)
    | Sig e1 e2 => Sig (lift c d e1) (lift (S c) d e2)
    | tt => tt
    | Unit => Unit
    | Eq e1 e2 e3 => Eq (lift c d e1) (lift c d e2) (lift c d e3)
    | Uni i => Uni i
    | Cust g => Cust g
    end.

  Fixpoint subst (e : t) (from : nat) (to : t) : t :=
    let rec_bind e := subst e (S from) (lift 0 1 to) in
    match e with
    | Var n => match lt_eq_lt_dec n from with
              | inleft (left _) => Var n
              | inleft (right _) => to
              | inright _ => Var (pred n)
              end
    | Lam e => Lam (rec_bind e)
    | App e1 e2 => App (subst e1 from to) (subst e2 from to)
    | Pi e1 e2 => Pi (subst e1 from to) (rec_bind e2)
    | Pair e1 e2 => Pair (subst e1 from to) (subst e2 from to)
    | Fst e => Fst (subst e from to)
    | Snd e => Snd (subst e from to)
    | Sig e1 e2 => Sig (subst e1 from to) (rec_bind e2)
    | tt => tt
    | Unit => Unit
    | Eq e1 e2 e3 => Eq (subst e1 from to) (subst e2 from to) (subst e3 from to)
    | Uni i => Uni i
    | Cust g => Cust g
    end.

  Definition eq_dec (e1 e2 : t) : {e1 = e2} + {e1 <> e2}.
    decide equality;
    auto using Nat.eq_dec, guid.eq_dec.
  Defined.

  Module wf.
    Fixpoint t (n : nat) (e : expr.t) : Prop :=
      match e with
      | Var i => i < n
      | Lam e => t (S n) e
      | App e1 e2 => t n e1 /\ t n e2
      | Pi e1 e2 => t n e1 /\ t (S n) e2
      | Pair e1 e2 => t n e1 /\ t n e2
      | Fst e => t n e
      | Snd e => t n e
      | Sig e1 e2 => t n e1 /\ t (S n) e2
      | tt => True
      | Unit => True
      | Eq e1 e2 e3 => t n e1 /\ t n e2 /\ t n e3
      | Uni i => True
      | Cust g => True
      end.

    Lemma lift :
      forall e n,
        t n e ->
        forall c d,
          t (n + d) (lift c d e).
    Proof.
      induction e; simpl; repeat (do_bool; intuition).
      - break_if; simpl; do_bool; omega.
      - apply IHe with (n := S n). auto.
      - apply IHe2 with (n := S n). auto.
      - apply IHe2 with (n := S n). auto.
    Qed.

    Lemma Forall_nth_error :
      forall A (P : A -> Prop) l n x,
        Forall P l ->
        nth_error l n = Some x ->
        P x.
    Proof.
      intros.
      prep_induction H.
      induction H; intros.
      - destruct n; discriminate.
      - destruct n; cbn [nth_error] in *.
        + find_inversion. auto.
        + eauto.
    Qed.

    Lemma Forall_map :
      forall A (P : A -> Prop) B (Q : B -> Prop) (f : A -> B) l,
        (forall a, P a -> Q (f a)) ->
        List.Forall P l ->
        List.Forall Q (List.map f l).
    Proof.
      induction 2; simpl; auto.
    Qed.

    Lemma lift_0_1:
      forall (n' : nat) (a : expr.t), t n' a -> t (S n') (expr.lift 0 1 a).
    Proof.
      intros. rewrite <- Nat.add_1_r. apply lift.  auto.
    Qed.

    Lemma subst :
      forall e from to,
        t (S from) e ->
        t from to ->
        t from (subst e from to).
    Proof.
      induction e; simpl; intuition auto using lift_0_1.
      repeat break_match; simpl; auto.
      omega.
    Qed.
  End wf.
End expr.

Module telescope.
  Definition t := list expr.t.

  Definition empty : t := [ ].

  (* Looking up an element of the telescope lifts the answer so that it is well
     formed in the telescope of *all* bindings of the telescope. *)
  Fixpoint nth (C : t) (i : nat) : option expr.t :=
    match C with
    | nil => None
    | cons e C => match i with
                 | 0 => Some (expr.lift 0 1 e)
                 | S i => match nth C i with
                         | None => None
                         | Some e => Some (expr.lift 0 1 e)
                         end
                 end
    end.

  Module wf.
    Fixpoint t (k : nat) (C : telescope.t) : Prop :=
      match C with
      | [] => True
      | e :: C => t k C /\ expr.wf.t (k + length C) e
      end.
  End wf.

  Lemma nth_wf :
    forall C k i e,
      wf.t k C ->
      nth C i = Some e ->
      expr.wf.t (k + length C) e.
  Proof.
    induction C; intros; destruct i; simpl in *; try discriminate.
    - find_inversion. break_and.
      rewrite <- plus_n_Sm.
      auto using expr.wf.lift_0_1.
    - break_and. break_match; try discriminate.
      find_inversion.
      rewrite <- plus_n_Sm.
      eauto using expr.wf.lift_0_1.
  Qed.
End telescope.

Module sequent.
  Record t : Type :=
    Make {
        context : telescope.t;
        goal : expr.t
    }.

  Module notations.
    Notation "H >> C" := (Make H C) (at level 61, right associativity) : sequent_scope.
    Bind Scope sequent_scope with sequent.t.
    Delimit Scope sequent_scope with sequent.
  End notations.

  Module wf.
    Definition t (S : sequent.t) : Prop :=
      let 'Make C G := S in telescope.wf.t 0 C /\ expr.wf.t (length C) G.
  End wf.
End sequent.

Module derivation.
  Inductive t : Type :=
  | Pi_Eq (D_A : t) (D_B : t) : t
  | Pi_Intro (i : nat) (D_A : t) (D_B : t) : t
  | Pi_Elim (H : nat) (a : expr.t) (D_A : t) (D_B : t) : t

  | Lam_Eq (i : nat) (D_A : t) (D_B : t) : t
  | Ap_Eq (i : nat) (pi_ty : expr.t) (D_fun D_arg D_cod : t) : t
  | Fun_Ext (D_lhs D_rhs : t) (D : t) : t

  | Sig_Eq (D_A : t) (D_B : t) : t
  | Sig_Intro (i : nat) (a : expr.t) (D_A D_B : t) (D_eq : t) : t
  | Sig_Elim (H : nat) (D_C : t) : t
  | Pair_Eq (i : nat) (D_A D_B : t) (D_ty : t) : t
  | Fst_Eq (sig_ty : expr.t) (D : t) : t
  | Snd_Eq (i : nat) (sig_ty : expr.t) (D_a D_B : t) : t

  | Unit_Eq : t
  | tt_Eq : t
  | Unit_Intro : t

  | Eq_Eq (D_ty D_lhs D_rhs : t) : t
  | Eq_Mem_Eq : t -> t
  | Eq_Sym : t -> t
  | Eq_Subst (i : nat) (a : expr.t) (D_ty : t) (D_eq D_body : t) : t

  | Uni_Eq : t
  | Cumulative : t -> t

  | Witness (w : expr.t) : t -> t

  | Cut (g : guid.t) : t -> t

  | Var (x : nat) : t
  | Var_Eq : t
  .

(*
  Module wf.
    Fixpoint t (n : nat) (D : t) : Prop :=
      match D with
      | derivation.Pi_Eq D_A D_B => t n D_A /\ t (S n) D_B
      | derivation.Pi_Intro i D_A D_B => t n D_A /\ t (S n) D_B
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
    End wf.
*)
End derivation.

Module extract.
  Fixpoint f (D : derivation.t) : expr.t :=
    match D with
    | derivation.Pi_Eq D_A D_B => expr.tt
    | derivation.Pi_Intro i D_A D_B => expr.Lam (f D_B)
    | derivation.Pi_Elim x a D_A D_B =>
      expr.subst (f D_B) 0 (expr.App (expr.Var x) a)
    | derivation.Lam_Eq i D_A D_B => expr.tt
    | derivation.Ap_Eq i pi_ty D_fun D_arg D_cod => expr.tt
    | derivation.Fun_Ext D_lhs D_rhs H => expr.tt
    | derivation.Sig_Eq _ _ => expr.tt
    | derivation.Sig_Intro i a D_A D_B D_eq => (expr.Pair a (f D_B))
    | derivation.Sig_Elim H D_C =>
      expr.subst (expr.subst (f D_C) 1 (expr.Fst (expr.Var H))) 0 (expr.Snd (expr.Var H))
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
      expr.subst (f D) 0 (expr.Cust g)
    | derivation.Var x => expr.Var x
    | derivation.Var_Eq => expr.tt
    end.
End extract.

(*
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
*)

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

  (*
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
  *)

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
  Notation "m >>= f" := (bind m f) (at level 61, right associativity) : tactic_monad.
  Notation "m1 >> m2" := (bind m1 (fun _ => m2)) (at level 61, right associativity) : tactic_monad.

  Notation "x <- m ;; f" := (bind m (fun x => f)) (at level 61, right associativity) : tactic_monad.
  End notations.

End tactic_monad.
Import tactic_monad.notations.

Module tactic_result.
  Record t (D G : Type) : Type :=
    Make {
        evidence : list D -> option D;
        goals : list G;
      }.
  Arguments Make {_ _} _ _.
End tactic_result.

Module Type TACTIC.
  Parameter derivation goal : Type.

  Definition result := tactic_result.t derivation goal.

  Definition t := forall R, goal -> tactic_monad.t R result.
End TACTIC.

Module tactic <: TACTIC.
  Definition derivation := derivation.t.
  Definition goal := sequent.t.

  Definition result := tactic_result.t derivation goal.

  Definition t := forall R, goal -> tactic_monad.t R result.
End tactic.

Module refiner.
  Module result.
    Inductive t :=
    | Proved : derivation.t -> (* extract: *) expr.t -> t
    | Incomplete : list sequent.t -> t
    | Failed : t
    .
  End result.

  Definition prove (thm : expr.t) (t : tactic.t) : result.t :=
    match tactic_monad.run (t _ (sequent.Make telescope.empty thm)) with
    | Some (tactic_result.Make ev gs) =>
      match gs with
      | [] => match ev [] with
             | None => result.Failed
             | Some d => result.Proved d (extract.f d)
             end
      | _ => result.Incomplete gs
      end
    | None => result.Failed
    end.
End refiner.

Definition option_bind {A B} (m : option A) (f : A -> option B) : option B :=
  match m with
  | None => None
  | Some a => f a
  end.

Module primitive_tactics (T : TACTIC).
  Definition id : T.t :=
    fun R g => tactic_monad.ret (tactic_result.Make
                                (fun l => List.hd_error l)
                                [g]).

  Definition choose (t1 t2 : T.t) : T.t :=
    fun R g => tactic_monad.choose [fun u => t1 R g; fun u => t2 R g].

  Fixpoint chunk (ns : list nat) (ds : list T.derivation) : list (list T.derivation) :=
    match ns with
    | [] => []
    | n :: ns => List.firstn n ds :: chunk ns (List.skipn n ds)
    end.

  Fixpoint zipAppOpt {A B} (fs : list (A -> B)) (xs : list A) : option (list B) :=
    match fs with
    | [] => match xs with
           | [] => Some []
           | _ => None
           end
    | f :: fs =>
      match xs with
      | [] => None
      | x :: xs => match zipAppOpt fs xs with
                  | None => None
                  | Some ys => Some (f x :: ys)
                  end
      end
    end.

  Fixpoint sequence_option {A} (l : list (option A)) : option (list A) :=
    match l with
    | [] => Some []
    | x :: xs => match x with
                | None => None
                | Some a => match sequence_option xs with
                           | None => None
                           | Some l => Some (a :: l)
                           end
                end
    end.

  Definition join_evidence (subresults : list T.result) (ds : list T.derivation)
    : option (list T.derivation) :=
    let derivChunks :=
          chunk (List.map (fun x => List.length (x.(tactic_result.goals))) subresults) ds in
    match zipAppOpt (List.map (fun x => x.(tactic_result.evidence)) subresults) derivChunks with
    | None => None
    | Some x => sequence_option x
    end.

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

  Definition unwrap {A R} (x : option A) : tactic_monad.t R A :=
    match x with
    | Some a => tactic_monad.ret a
    | None => tactic_monad.fail
    end.

  Definition split (t : T.t) (ts : list T.t) : T.t :=
    fun R g =>
      r <- t R g ;;
      let 'tactic_result.Make evidence goals := r in
      pf <- assume_sb (Nat.eq_dec (length ts) (length goals)) ;;
      rs <- unwrap (zipAppOpt (List.map (fun t => t R) ts) goals) ;;
      subs <- tactic_monad.sequence rs ;;
      tactic_monad.ret (tactic_result.Make
                          (fun ds => option_bind (join_evidence subs ds) evidence)
                          (List.flat_map (fun x => x.(tactic_result.goals)) subs)).

  Definition next (t1 t2 : T.t) : T.t :=
    fun R g =>
      r <- t1 R g ;;
      let 'tactic_result.Make evidence goals := r in
      rs <- tactic_monad.sequence (List.map (t2 R) goals) ;;
      tactic_monad.ret (tactic_result.Make
                          (fun ds => option_bind (join_evidence rs ds) evidence)
                          (List.flat_map (fun x => x.(tactic_result.goals)) rs)).

  Definition try (t : T.t) : T.t :=
    choose t id.

  Fixpoint repeat (k : nat) (t : T.t) : T.t :=
    match k with
    | 0 => id
    | S k => try (next t (repeat k t))
    end.
End primitive_tactics.

Module P := primitive_tactics tactic.

Module rules.
  Import P.
  Import tactic_monad.
  Local Open Scope tactic_monad.

  Import sequent.notations.
  Local Open Scope sequent.

  Definition nullary_derivation (d : derivation.t) :=
    tactic_result.Make(G:=sequent.t) (fun _ => Some d) [].

  Definition unary_derivation (d : derivation.t -> derivation.t) g :=
    tactic_result.Make(G:=sequent.t) (fun l => match l with
                                            | [x]  => Some (d x)
                                            | _ => None
                                            end) [g].

  Definition binary_derivation (d : derivation.t -> derivation.t -> derivation.t) g1 g2 :=
    tactic_result.Make(G:=sequent.t)
      (fun l => match l with
             | [d1; d2] => Some (d d1 d2)
             | _ => None
             end)
      [g1; g2].

  Definition ternary_derivation (d : derivation.t -> derivation.t ->
                                     derivation.t -> derivation.t) g1 g2 g3 :=
    tactic_result.Make(G:=sequent.t)
      (fun l => match l with
             | [d1; d2; d3] => Some (d d1 d2 d3)
             | _ => None
             end)
      [g1; g2; g3].


  Module unit.
    (* H >> unit = unit in U(i) *)
    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> (expr.Eq expr.Unit expr.Unit (expr.Uni _)) =>
        ret (nullary_derivation derivation.Unit_Eq)
      | _ => fail
      end.

    (* H >> unit *)
    Definition Intro : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Unit => ret (nullary_derivation derivation.Unit_Intro)
      | _ => fail
      end.

    (* H >> tt = tt in unit *)
    Definition TTEq : tactic.t :=
      fun R g =>
      match g with
      | H >> (expr.Eq expr.tt expr.tt expr.Unit) =>
        ret (nullary_derivation derivation.tt_Eq)
      | _ => fail
      end.
  End unit.

  Module pi.

    (* H >> x:A -> B = x:A' -> B' in U(i)
         H >> A = A' in U(i)
         H, x:A >> B = B' in U(i) *)
    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.Pi A B) (expr.Pi A' B') (expr.Uni i) =>
        ret (binary_derivation derivation.Pi_Eq
                (H >> (expr.Eq A A' (expr.Uni i)))
                (A :: H >> (expr.Eq B B' (expr.Uni i))))
      | _ => fail
      end.

    (* H >> x:A -> B
         H >> A = A in U(i)
         H, x:A >> B *)
    Definition Intro (i : nat) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Pi A B =>
        ret (binary_derivation (derivation.Pi_Intro i)
                (H >> expr.Eq A A (expr.Uni i))
                (A :: H >> B))
      | _ => fail
      end.

    (* H >> C
         H(n) = x:A -> B
         H >> e = e in A
         H, [e/x]B >> C
     *)
    Definition Elim (n : nat) (e : expr.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        ty <- unwrap (telescope.nth H n) ;;
        match ty with
        | expr.Pi A B =>
          ret (binary_derivation (derivation.Pi_Elim n e)
                  (H >> expr.Eq e e A)
                  (expr.subst B 0 e :: H >> expr.lift 0 1 C))
        | _ => fail
        end
      end.

    (* H >> \x.e = \x.e' in x:A -> B
         H >> A = A in U(i)
         H, x:A >> e = e' in B *)
    Definition LamEq (i : nat) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.Lam e) (expr.Lam e') (expr.Pi A B) =>
        ret (binary_derivation (derivation.Lam_Eq i)
                (H >> expr.Eq A A (expr.Uni i))
                (A :: H >> expr.Eq e e' B))
      | _ => fail
      end.

    (* H >> n1 m1 = n2 m2 in T
         H >> n1 = n2 in x:A -> B
         H >> m1 = m2 in A
         H >> [n1/x]B = T in U(i) *)
    Definition ApEq (i : nat) (ty : expr.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.App n1 m1) (expr.App n2 m2) T =>
        match ty with
        | expr.Pi A B =>
          ret (ternary_derivation (derivation.Ap_Eq i (expr.Pi A B))
                  (H >> expr.Eq n1 n2 (expr.Pi A B))
                  (H >> expr.Eq m1 m2 A)
                  (H >> expr.Eq (expr.subst B 0 n1) T (expr.Uni i)))
        | _ => fail
        end
      | _ => fail
      end.

    (* H >> e1 = e2 in x:A -> B
           H >> e1 = e1 in x:A -> B
           H >> e2 = e2 in x:A -> B
           H, x:A >> e1 x = e2 x in B *)
    Definition FunExt : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq e1 e2 (expr.Pi A B) =>
        ret (ternary_derivation derivation.Fun_Ext
                (H >> expr.Eq e1 e1 (expr.Pi A B))
                (H >> expr.Eq e2 e2 (expr.Pi A B))
                (A :: H >> expr.Eq (expr.App (expr.lift 0 1 e1) (expr.Var 0))
                                   (expr.App (expr.lift 0 1 e2) (expr.Var 0))
                                   B))

      | _ => fail
      end.
  End pi.

  Module uni.
    (* H >> U(i) = U(i) in U(i+1) *)
    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.Uni i) (expr.Uni j) (expr.Uni k) =>
        _ <- assume_sb (Nat.eq_dec i j) ;;
        _ <- assume_sb (Nat.eq_dec (S i) k) ;;
        ret (nullary_derivation derivation.Uni_Eq)
      | _ => fail
      end.

    (* H >> A = B in U(i+1)
         H >> A = B in U(i) *)
    Definition Cumulative : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq A B (expr.Uni (S i)) =>
        ret (unary_derivation derivation.Cumulative
                (H >> expr.Eq A B (expr.Uni i)))
      | _ => fail
      end.
  End uni.

  Module general.
    (* H >> C
         H(n) = C *)
    Definition Hyp (n : nat) : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        ty <- unwrap (telescope.nth H n) ;;
        _ <- assume_sb (expr.eq_dec C ty) ;;
        ret (nullary_derivation (derivation.Var n))
      end.

    (* H >> x = x in A
         H(x) = A *)
    Definition HypEq : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.Var n1) (expr.Var n2) A =>
        _ <- assume_sb (Nat.eq_dec n1 n2) ;;
        ty <- unwrap (telescope.nth H n1) ;;
        _ <- assume_sb (expr.eq_dec A ty) ;;
        ret (nullary_derivation derivation.Var_Eq)
      | _ => fail
      end.
  End general.

  Module eq.
    (* H >>   m1 = n1 in A1   =   m2 = n2 in A2   in U(i)
           H >> A1 = A2 in U(i)
           H >> m1 = m2 in A1
           H >> n1 = n2 in A1 *)
    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.Eq m1 n1 A1) (expr.Eq m2 n2 A2) (expr.Uni i) =>
        ret (ternary_derivation derivation.Eq_Eq
                (H >> expr.Eq A1 A2 (expr.Uni i))
                (H >> expr.Eq m1 m2 A1)
                (H >> expr.Eq n1 n2 A1))
      | _ => fail
      end.
  End eq.

  Import expr.exports.
  Import expr.notations.
  Local Open Scope expr.

  Module sig.
    (* H >> x:A * B = x:A' * B' in U(i)
           H >> A = A' in U(i)
           H, x:A >> B = B' in U(i) *)
    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >>  A * B = A' * B' in expr.Uni i =>
        ret (binary_derivation derivation.Sig_Eq
               (H >> A = A' in expr.Uni i)
               (A :: H >> B = B' in expr.Uni i))
      | _ => fail
      end.

    (* H >> x:A * B
         H >> a = a in A
         H >> [a/x]B
         H, x:A >> B = B in U(i) *)
    Definition Intro (i : nat) (a : expr.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> A * B =>
        ret (ternary_derivation (derivation.Sig_Intro i a)
                (H >> a = a in A)
                (H >> expr.subst B 0 a)
                (A :: H >> B = B in Uni i))
      | _ => fail
      end.

    (* H >> C
         H(n) = x:A * B
         H, x:A, B >> C *)
    Definition Elim (n : nat) : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        ty <- unwrap (telescope.nth H n) ;;
        match ty with
        | A * B =>
          ret (unary_derivation (derivation.Sig_Elim n)
                (B :: A :: H >> expr.lift 0 2 C))
        | _ => fail
        end
      end.

    (* H >> (a,b) = (a',b') in x:A * B
         H >> a = a' in A
         H >> b = b' in [a/x]B
         H, x:A >> B = B in U(i) *)
    Definition PairEq (i : nat) : tactic.t :=
      fun R g =>
      match g with
      | H >> (a,b) = (a',b') in A * B =>
        ret (ternary_derivation (derivation.Pair_Eq i)
                (H >> a = a' in A)
                (H >> b = b' in expr.subst B 0 a)
                (A :: H >> B = B in Uni i))
      | _ => fail
      end.

    (* H >> fst m1 = fst m2 in A
         H >> m1 = m2 in A * B
     *)
    Definition FstEq (B : expr.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Fst m1 = expr.Fst m2 in A =>
        ret (unary_derivation (derivation.Fst_Eq B)
                (H >> m1 = m2 in A * B))
      | _ => fail
      end.


    (* H >> snd m1 = snd m2 in C
         H >> m1 = m2 in x:A * B
         H >> [fst m1/x]B = C in U(i) *)
    Definition SndEq (i : nat) (ty : expr.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Snd m1 = expr.Snd m2 in C =>
        match ty with
        | A * B =>
          ret (binary_derivation (derivation.Snd_Eq i ty)
                 (H >> m1 = m2 in A * B)
                 (H >> expr.subst B 0 (Fst m1) = C in Uni i))
        | _ => fail
        end
      | _ => fail
      end.
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

  Module exports.
    Coercion Var : String.string >-> t.
    Coercion App : t >-> Funclass.
    Coercion Cust : guid.t >-> t.

    Notation Fst := Fst.
    Notation Snd := Snd.
    Notation tt := tt.
    Notation Unit := Unit.
    Notation Uni := Uni.
  End exports.

  Module notations.
    Bind Scope ast_scope with ast.t.
    Delimit Scope ast_scope with ast.
    Import String.

    Notation "'\' x ',' e" := (ast.Lam x e) (at level 50) : ast_scope.
    Notation "{ x : A } -> B" := (ast.Pi x A B) (at level 0, x at level 99, B at level 200) : ast_scope.
    Notation "A -> B" := (ast.Pi "_" A B) (at level 99, B at level 200).

    Notation "( x , y , .. , z )" := (ast.Pair .. (ast.Pair x y) .. z) : ast_scope.
    Notation "{ x : A } * B" := (ast.Sig x A B) (at level 0, x at level 99, B at level 200) : ast_scope.
    Notation "A * B" := (ast.Sig "_" A B) : ast_scope.
    Notation "A = B 'in' C" := (ast.Eq A B C) (at level 50) : ast_scope.

    Local Open Scope ast.
    Import String.
    Local Open Scope string.
    Import exports.

    Check (\ "x", "x").
    Check (\ "x", "x") (\ "x", "x").
    Check {"x" : "A"} -> "B".
    Check ("x", "x").
    Check {"_" : (\ "x", "x")} * (\ "x", "x").
    Check (\ "x", "x") = (\ "x", "x") in Unit.
  End notations.


  (* Helper function to find the first occurence of a particular value in a list. *)
  Fixpoint index_of {A} (A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
           (a : A)
           (l : list A) : option nat :=
    match l with
    | [] => None
    | a' :: l => if A_eq_dec a a'
                then Some 0
                else match index_of A_eq_dec a l with
                     | None => None
                     | Some i => Some (S i)
                     end
    end.

  Fixpoint to_expr' (l : list String.string) (a : t) : option expr.t :=
    match a with
    | Var s =>
      match index_of String.string_dec s l with
      | Some i => Some (expr.Var i)
      | None => None
      end
    | Lam s a =>
      match to_expr' (s :: l) a with None => None
      | Some a => Some (expr.Lam a)
      end
    | App a1 a2 =>
      match to_expr' l a1 with None => None
      | Some a1 =>
      match to_expr' l a2 with None => None
      | Some a2 => Some (expr.App a1 a2)
      end end
    | Pi s a1 a2 =>
      match to_expr' l a1 with None => None
      | Some a1 =>
      match to_expr' (s :: l) a2 with None => None
      | Some a2 => Some (expr.Pi a1 a2)
      end end
    | Pair a1 a2 =>
      match to_expr' l a1 with None => None
      | Some a1 =>
      match to_expr' l a2 with None => None
      | Some a2 => Some (expr.Pair a1 a2)
      end end
    | Fst a =>
      match to_expr' l a with None => None
      | Some a => Some (expr.Fst a)
      end
    | Snd a =>
      match to_expr' l a with None => None
      | Some a => Some (expr.Snd a)
      end
    | Sig s a1 a2 =>
      match to_expr' l a1 with None => None
      | Some a1 =>
      match to_expr' (s :: l) a2 with None => None
      | Some a2 => Some (expr.Sig a1 a2)
      end end
    | tt => Some expr.tt
    | Unit => Some expr.Unit
    | Eq a1 a2 a3 =>
      match to_expr' l a1 with None => None
      | Some a1 =>
      match to_expr' l a2 with None => None
      | Some a2 =>
      match to_expr' l a3 with None => None
      | Some a3 => Some (expr.Eq a1 a2 a3)
      end end end
    | Uni i => Some (expr.Uni i)
    | Cust g => Some (expr.Cust g)
    end.

  Fixpoint to_expr (a : t) : option expr.t :=
    to_expr' [] a.

End ast.

Open Scope string_scope.

(* Here's an actually interesting theorem: function extensionality. Much *much*
   nicer to write this as an ast than as an expr! *)
Import ast.exports.
Import ast.notations.

Definition ast_funext : ast.t :=
  {"A" : Uni 0} ->
  {"B" : Uni 0} ->
  {"f" : "A" -> "B"} ->
  {"g" : "A" -> "B"} ->
  ({"x" : "A"} -> "f" "x" = "g" "x" in "B") ->
  "f" = "g" in ("A" -> "B").

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
Ltac parse' l e :=
  let e := eval compute in (ast.to_expr' l e)
  in match e with
     | Some ?x => exact x
     end.

(* We can use `parse` to conveniently define the expr for function
   extensionality without copy-pasting. *)
Definition funext : expr.t := ltac:(parse ast_funext).

(* A few simple notations for the tactics. *)
Notation "t ;; l" := (P.split t l) (at level 50, left associativity).
Notation "t1 ;;; t2" := (P.next t1 t2) (at level 50, left associativity).
Notation "t1 || t2" := (P.choose t1 t2).

Module tac_info.
  Record t :=
    Make {
        i : option nat;
        e : option expr.t
      }.

  Definition empty : t := Make None None.
  Definition level (i : nat) : t := Make (Some i) None.
  Definition arg (e : expr.t) : t := Make None (Some e).

  Definition get_i (x : t) {R} : tactic_monad.t R nat :=
    match i x with
    | Some i => tactic_monad.ret i
    | None => tactic_monad.fail
    end.

  Definition get_e (x : t) {R} : tactic_monad.t R expr.t :=
    match e x with
    | Some e => tactic_monad.ret e
    | None => tactic_monad.fail
    end.
End tac_info.

Module tac.
  Definition Intro (info : tac_info.t) : tactic.t.
    refine (fun R g => _).
    refine (tactic_monad.choose
              [fun _ => unit.Intro g;
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i => pi.Intro i g);
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i =>
                     tactic_monad.bind (tac_info.get_e info) (fun e => sig.Intro i e g))]).
  Defined.

  Definition Eq (info : tac_info.t) : tactic.t.
    refine (fun R g => _).
    refine (tactic_monad.choose
              [fun _ => unit.Eq g;
               fun _ => pi.Eq g;
               fun _ => sig.Eq g;
               fun _ => uni.Eq g;
               fun _ => eq.Eq g;
               fun _ => unit.TTEq g;
               fun _ => general.HypEq g;
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i => pi.LamEq i g);
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i => sig.PairEq i g)
           ]).
  Defined.

  Import sequent.notations.
  Local Open Scope sequent.

  Definition Assumption : tactic.t.
    refine (fun R g => _).
    refine (let fix go k :=
                match k with
                | 0 => P.id g
                | S k => tactic_monad.choose [fun _ => general.Hyp k g; fun _ => go k]
                end in _).
    exact (match g with
           | H >> _ => go (length H)
           end).
  Defined.
End tac.

Import sequent.notations.
Open Scope sequent.

(* Let's prove function extensionality! *)
Eval cbv in
  let go_eq := P.repeat 10 (tac.Eq tac_info.empty) in
  refiner.prove funext
                (pi.Intro 1 ;;; go_eq ;;;
                 pi.Intro 1 ;;; go_eq ;;;
                 pi.Intro 0 ;;; go_eq ;;;
                 pi.Intro 0 ;;; go_eq ;;;
                 pi.Intro 0 ;;; go_eq ;; [
                        pi.ApEq 0
                           (ltac:(parse' ["x"; "g"; "f"; "B"; "A"]
                                                    (ast.Pi "_" "A" "B")));;; go_eq;
                        pi.ApEq 0
                           (ltac:(parse' ["x"; "g"; "f"; "B"; "A"]
                                                    (ast.Pi "_" "A" "B")));;; go_eq;

                        pi.FunExt;;; go_eq ;;;
                        pi.Elim 1
                          (ltac:(parse' ["x"; "H"; "g"; "f"; "B"; "A"] "x"));;;
                          go_eq;;;
                        tac.Assumption]).

Definition ast_proj1 : ast.t :=
  {"A" : Uni 0} ->
  {"B" : "A" -> Uni 0} ->
  ({"x" : "A"} * "B" "x") ->
  "A".

Definition proj1 : expr.t := ltac:(parse ast_proj1).

Eval cbv in refiner.prove proj1
  (pi.Intro 1;; [uni.Eq;
   pi.Intro 1;; [pi.Eq;; [uni.Cumulative;;; general.HypEq; uni.Eq];
   pi.Intro 0;; [sig.Eq;; [general.HypEq;
       pi.ApEq 1
         (ltac:(parse' ["x"; "B"; "A"] (ast.Pi "y" "A" (ast.Uni 0))));;
       [general.HypEq; general.HypEq; uni.Eq]];
   sig.Elim 0;; [general.Hyp 1]]]]).


Definition ast_snd_eq : ast.t :=
  Snd (tt, tt) = Snd (tt, tt) in Unit.

Definition snd_eq : expr.t := ltac:(parse ast_snd_eq).

Eval cbv in refiner.prove snd_eq
   (sig.SndEq 0 (ltac:(parse (ast.Sig "_" ast.Unit ast.Unit))) ;;
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
      (fun _ => result.t)
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
