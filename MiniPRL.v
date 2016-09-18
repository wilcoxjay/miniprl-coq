(* A Coq port of MiniPRL [1].
   A longer term goal is to implement some of the ideas of Verified NuPRL [2].

   [1]: https://github.com/jozefg/miniprl
   [2]: http://www.nuprl.org/html/Nuprl2Coq/ *)
Require String.
Require Import List Bool Arith.
Require Omega. (* do not import; conflicts with "~" notation *)
Import ListNotations.

Ltac omega := Omega.omega. (* sigh... *)

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

  | Ceq : t -> t -> t

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
    Notation "A = B 'in' C" := (expr.Eq A B C) (at level 70, B at next level) : expr_scope.

    Notation "A ~ B" := (expr.Ceq A B) (at level 70) : expr_scope.

    Local Open Scope expr.
    Import exports.

    Check (\ 0).
    Check (\ 0) (\ 0).
    Check (\ 0) -> (\ 0).
    Check (0, 0).
    Check (\ 0) * (\ 0).
    Check (\ 0) = (\ 0) in Unit.
    Check ((\ 0) ~ (\ 0) )%expr.

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
    | Ceq e1 e2 => Ceq (lift c d e1) (lift c d e2)
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
    | Ceq e1 e2 => Ceq (subst e1 from to) (subst e2 from to)
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
      | Ceq e1 e2 => t n e1 /\ t n e2
      | Uni i => True
      | Cust g => True
      end.

    Fixpoint dec (n : nat) (e : expr.t) {struct e} : {t n e} + {~ t n e}.
      refine match e as e0 return {t n e0} + {~ t n e0} with
      | Var i => lt_dec _ _
      | Lam e => dec (S n) e
      | App e1 e2 =>
        match dec n e1 with
        | left _ => match dec n e2 with
                   | left _ => left (conj _ _)
                   | right _ => right _
                   end
        | right _ => right _
        end
      | Pi e1 e2 =>
        match dec n e1 with
        | left _ => match dec (S n) e2 with
                   | left _ => left (conj _ _)
                   | right _ => right _
                   end
        | right _ => right _
        end
      | Pair e1 e2 =>
        match dec n e1 with
        | left _ => match dec n e2 with
                   | left _ => left (conj _ _)
                   | right _ => right _
                   end
        | right _ => right _
        end
      | Fst e => dec n e
      | Snd e => dec n e
      | Sig e1 e2 =>
        match dec n e1 with
        | left _ => match dec (S n) e2 with
                   | left _ => left (conj _ _)
                   | right _ => right _
                   end
        | right _ => right _
        end
      | tt => left I
      | Unit => left I
      | Eq e1 e2 e3 =>
        match dec n e1 with
        | left _ => match dec n e2 with
                   | left _ => match dec n e3 with
                              | left _ => left _
                              | right _ => right _
                              end
                   | right _ => right _
                   end
        | right _ => right _
        end
      | Ceq e1 e2 =>
        match dec n e1 with
        | left _ => match dec n e2 with
                   | left _ => left (conj _ _)
                   | right _ => right _
                   end
        | right _ => right _
        end
      | Uni i => left I
      | Cust g => left I
      end; simpl; intuition.
    Defined.

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

    Lemma lift':
      forall (n c d : nat) (a : expr.t), t n a -> t (d + n) (expr.lift c d a).
    Proof.
      intros. rewrite <- Nat.add_comm. apply lift.  auto.
    Qed.

    Lemma lift_0_1:
      forall (n' : nat) (a : expr.t), t n' a -> t (S n') (expr.lift 0 1 a).
    Proof.
      intros. apply lift' with (d := 1). auto.
    Qed.

    Lemma subst :
      forall e n from to,
        t (S n) e ->
        t n to ->
        from <= n ->
        t n (expr.subst e from to).
    Proof.
      induction e; simpl; intuition auto using lift_0_1 with arith.
      repeat break_match; simpl; auto; omega.
    Qed.
  End wf.
End expr.

Module value.
  Inductive t : expr.t -> Prop :=
  | Lam : forall e, t (expr.Lam e)
  | Pi : forall e1 e2, t (expr.Pi e1 e2)
  | tt : t expr.tt
  | Unit : t expr.Unit
  | Eq : forall e1 e2 e3, t (expr.Eq e1 e2 e3)
  | Ceq : forall e1 e2, t (expr.Ceq e1 e2)
  | Uni : forall i, t (expr.Uni i)
  | Cust : forall g, t (expr.Cust g)
  | Pair : forall e1 e2, t (expr.Pair e1 e2)
  | Sig : forall e1 e2, t (expr.Sig e1 e2)
  .
  Hint Constructors t.
End value.

Module step.
  Module result.
    Inductive t :=
    | Step : expr.t -> t
    | Value : t
    | Stuck : t
    .
  End result.

  Inductive t : expr.t -> expr.t -> Prop :=
  | Beta : forall e1 e2, t (expr.App (expr.Lam e1) e2) (expr.subst e1 0 e2)
  | AppL : forall e1 e1' e2, t e1 e1' -> t (expr.App e1 e2) (expr.App e1' e2)
  | FstPair : forall e1 e2, t (expr.Fst (expr.Pair e1 e2)) e1
  | SndPair : forall e1 e2, t (expr.Snd (expr.Pair e1 e2)) e2
  | Fst : forall e e', t e e' -> t (expr.Fst e) (expr.Fst e')
  | Snd : forall e e', t e e' -> t (expr.Snd e) (expr.Snd e')
  .
  Hint Constructors t.

  Lemma det : forall e e1 e2, t e e1 -> t e e2 -> e1 = e2.
  Proof.
    intros.
    generalize dependent e2.
    induction H; intros.
    - invc H0.
      + auto.
      + solve_by_inversion.
    - invc H0.
      + solve_by_inversion.
      + f_equal; auto.
    - invc H0.
      + auto.
      + solve_by_inversion.
    - invc H0.
      + auto.
      + solve_by_inversion.
    - invc H0.
      + solve_by_inversion.
      + f_equal; auto.
    - invc H0.
      + solve_by_inversion.
      + f_equal; auto.
  Qed.

  Fixpoint f (e : expr.t) : result.t :=
    match e with
    | expr.Var n => result.Stuck
    | expr.Lam e => result.Value
    | expr.App e1 e2 =>
      match f e1 with
      | result.Stuck => result.Stuck
      | result.Value => match e1 with
                       | expr.Lam e1 => result.Step (expr.subst e1 0 e2)
                       | _ => result.Stuck
                       end
      | result.Step e1' => result.Step (expr.App e1' e2)
      end
    | expr.Pi e1 e2 => result.Value
    | expr.Pair e1 e2 => result.Value
    | expr.Fst e =>
      match f e with
      | result.Stuck => result.Stuck
      | result.Value => match e with
                       | expr.Pair e1 e2 => result.Step e1
                       | _ => result.Stuck
                       end
      | result.Step e' => result.Step (expr.Fst e')
      end
    | expr.Snd e =>
      match f e with
      | result.Stuck => result.Stuck
      | result.Value => match e with
                       | expr.Pair e1 e2 => result.Step e2
                       | _ => result.Stuck
                       end
      | result.Step e' => result.Step (expr.Snd e')
      end
    | expr.Sig e1 e2 => result.Value
    | expr.tt => result.Value
    | expr.Unit => result.Value
    | expr.Eq e1 e2 e3 => result.Value
    | expr.Ceq e1 e2 => result.Value
    | expr.Uni i => result.Value
    | expr.Cust g => result.Value
    end.

  Lemma f_t :
    forall e, match f e with
         | result.Step e' => t e e'
         | result.Value => value.t e
         | result.Stuck => (forall e', ~ t e e') /\ ~ value.t e
         end.
  Proof.
    induction e; simpl; auto.
    - intuition; solve_by_inversion.
    - destruct (f e1).
      + auto.
      + invcs IHe1; intuition; invc H; try solve_by_inversion.
      + intuition; invc H1; eauto.
    - destruct (f e).
      + auto.
      + invcs IHe; intuition; invc H; try solve_by_inversion.
      + intuition; invc H1; eauto.
    - destruct (f e).
      + auto.
      + invcs IHe; intuition; invc H; try solve_by_inversion.
      + intuition; invc H1; eauto.
  Qed.
End step.

Module star.
  Definition t : expr.t -> expr.t -> Prop := Relation_Operators.clos_refl_trans_1n _ step.t.
End star.

Module eval.
  Definition t (e : expr.t) (v : expr.t) : Prop :=
    star.t e v /\ value.t v.
End eval.

Module run.
  Fixpoint f (n : nat) (e : expr.t) : option expr.t :=
    match n with
    | 0 => Some e
    | S n => match step.f e with
            | step.result.Step e' => f n e'
            | step.result.Value => Some e
            | step.result.Stuck => None
            end
    end.
End run.

Lemma nth_error_firstn_skipn:
  forall (A : Type) (C : list A) (i : nat) (e : A),
    nth_error C i = Some e -> firstn i C ++ e :: skipn (S i) C = C.
Proof.
  induction C; destruct i; intros; try discriminate.
  - simpl in *. congruence.
  - simpl in H. apply IHC in H.
    change (firstn _ _) with (a :: firstn i C).
    change (skipn _ _) with (skipn (S i) C).
    cbn [app].
    now rewrite H.
Qed.

Lemma firstn_skipn_length :
  forall A n (l : list A), length (firstn n l) + length (skipn n l) = length l.
Proof.
  intros.
  rewrite <- app_length.
  f_equal.
  apply firstn_skipn.
Qed.


Lemma firstn_snoc :
  forall A n l (a : A),
    nth_error l n = Some a ->
    firstn n l ++ [a] = firstn (S n) l.
Proof.
  induction n; destruct l; intros.
  - simpl in *. discriminate.
  - simpl in *. congruence.
  - simpl in *. discriminate.
  - simpl in H. apply IHn in H.
    change (firstn (S n) _) with (a :: firstn n l).
    change (firstn (S (S n)) _) with (a :: firstn (S n) l).
    cbn [app].
    auto using f_equal.
Qed.

Module binding.
  Definition t (E : Type) : Type := String.string * E.
End binding.

Module outermost_first_telescope.
  (* The head of the list is the *least* recently bound variable. *)
  Definition t E := list (binding.t E).

  Fixpoint lift (c d : nat) (C : t expr.t) : t expr.t :=
    match C with
    | [] => []
    | (n,e) :: C => (n, expr.lift c d e) :: lift (S c) d C
    end.

  Fixpoint subst (C : t expr.t) (from : nat) (to : expr.t) : t expr.t :=
    match C with
    | [] => []
    | (n, e) :: C => (n, expr.subst e from to) :: subst C (S from) (expr.lift 0 1 to)
    end.

  Module wf.
    Fixpoint t (k : nat) (C : t expr.t) : Prop :=
      match C with
      | [] => True
      | (_, e) :: C => expr.wf.t k e /\ t (S k) C
      end.

    Lemma app : forall C1 C2 n,
        outermost_first_telescope.wf.t n C1 ->
        outermost_first_telescope.wf.t (n + length C1) C2 ->
        outermost_first_telescope.wf.t n (C1 ++ C2).
    Proof.
      induction C1; simpl; repeat break_match; intuition.
      - eapply eq_rect with (P := fun x => _ x _); eauto.
      - apply IHC1; auto.
        eapply eq_rect with (P := fun x => _ x _); eauto.
        omega.
    Qed.
  End wf.
End outermost_first_telescope.

Module telescope.
  (* The head of the list is the *most* recently bound variable. *)
  Definition t E := list (binding.t E).

  Definition names E (C : t E) : list String.string := map (@fst _ _) C.

  (* Looking up an element of the telescope lifts the answer so that it is well
     formed in the telescope of *all* bindings of the telescope. *)
  Fixpoint nth (C : t expr.t) (i : nat) : option expr.t :=
    match C with
    | [] => None
    | (n, e) :: C => match i with
                 | 0 => Some (expr.lift 0 1 e)
                 | S i => match nth C i with
                         | None => None
                         | Some e => Some (expr.lift 0 1 e)
                         end
                 end
    end.

  Definition split E (C : t E) (i : nat) : option (t E * binding.t E * t E) :=
    match nth_error C i with
    | None => None
    | Some e => Some (firstn i C, e, skipn (S i) C)
    end.

  Lemma nth_length C : forall i e, nth C i = Some e -> i < length C.
  Proof.
    induction C; simpl; intros.
    - discriminate.
    - repeat break_match; try discriminate.
      + find_inversion. omega.
      + find_inversion. eauto using lt_n_S.
  Qed.

  Lemma split_app : forall E C i C1 (e : binding.t E) C2,
      split C i = Some (C1, e, C2) ->
      C1 ++ e :: C2 = C.
  Proof.
    unfold split.
    intros.
    break_match; try discriminate.
    match goal with
    | [ H : Some (?a, ?b, ?c) = Some (?d, ?e, ?f) |- _ ] =>
      (assert (a = d /\ b = e /\ c = f) by (intuition congruence)); clear H; repeat break_and; subst
    end.
    auto using nth_error_firstn_skipn.
  Qed.

  Definition to_outer E (C : t E) : outermost_first_telescope.t E := rev C.
  Definition from_outer E (C : outermost_first_telescope.t E) : t E := rev C.

  Definition lift (c d : nat) (C : t expr.t) : t expr.t :=
    from_outer (outermost_first_telescope.lift c d (to_outer C)).

  Definition subst (C : t expr.t) (from : nat) (to : expr.t) : t expr.t :=
    from_outer (outermost_first_telescope.subst (to_outer C) from to).

  Module wf.
    Fixpoint t (k : nat) (C : t expr.t) : Prop :=
      match C with
      | [] => True
      | (_,e) :: C => t k C /\ expr.wf.t (k + length C) e
      end.

    Lemma nth :
      forall C k i e,
        nth C i = Some e ->
        wf.t k C ->
        expr.wf.t (k + length C) e.
    Proof.
      induction C; intros; destruct i; simpl in *; repeat break_let; try discriminate.
      - find_inversion. break_and.
        rewrite <- plus_n_Sm.
        auto using expr.wf.lift_0_1.
      - break_and. break_match; try discriminate.
        find_inversion.
        rewrite <- plus_n_Sm.
        eauto using expr.wf.lift_0_1.
    Qed.

    Lemma firstn :
      forall (n : nat) C (k : nat), wf.t k C -> wf.t (length (skipn n C) + k) (firstn n C).
    Proof.
      induction n; simpl; intros.
      + auto.
      + break_match; simpl in *; repeat break_let; intuition.
        pose proof firstn_skipn_length n t1.
        eapply eq_rect with (P := fun x => expr.wf.t x _).
        eauto.
        omega.
    Qed.

    Lemma skipn :
      forall (n : nat) C (k : nat), wf.t k C -> wf.t k (skipn n C).
    Proof.
      induction n; simpl; intros.
      + auto.
      + break_match; simpl in *; repeat break_let; intuition.
    Qed.


    Lemma app_inv :
      forall C1 C2 k,
        wf.t k (C1 ++ C2) ->
        wf.t (length C2 + k) C1 /\ wf.t k C2.
    Proof.
      induction C1; simpl; intros.
      - intuition.
      - repeat break_let. break_and.
        apply IHC1 in H. break_and.
        intuition.
        rewrite app_length in *.
        eapply eq_rect with (P := fun x => _ x _); eauto.
        omega.
    Qed.

    Lemma split : forall C k i C1 n e C2,
        split C i = Some (C1, (n, e), C2) ->
        wf.t k C ->
        wf.t (S (length C2 + k)) C1 /\ expr.wf.t (length C2 + k) e /\ wf.t k C2.
    Proof.
      unfold split.
      intros.
      break_match; try discriminate.
      match goal with
      | [ H : Some (?a, ?b, ?c) = Some (?d, ?e, ?f) |- _ ] =>
        (assert (a = d /\ b = e /\ c = f) by (intuition congruence));
        clear H; repeat break_and; subst
      end.
      pose proof nth_error_firstn_skipn _ _ Heqo.
      rewrite <- H in H0.
      apply app_inv in H0. break_and.
      cbn [wf.t] in H1. break_and.
      cbn [length] in *.
      intuition.
      eapply eq_rect with (P := fun x => _ x _); eauto.
      omega.
    Qed.

    Lemma app :
      forall C1 C2 k,
        wf.t (length C2 + k) C1 ->
        wf.t k C2 ->
        wf.t k (C1 ++ C2).
    Proof.
      induction C1; simpl; repeat break_let; intuition.
      rewrite app_length.
      eapply eq_rect with (P := fun x => _ x _); eauto.
      omega.
    Qed.

    Lemma to_outer_wf : forall C n, telescope.wf.t n C -> outermost_first_telescope.wf.t n (to_outer C).
    Proof.
      unfold to_outer.
      induction C; intros.
      - auto.
      - simpl in H. break_let; break_and. simpl.
        apply outermost_first_telescope.wf.app; auto.
        simpl. rewrite rev_length. auto.
    Qed.

    Lemma from_outer_wf : forall C n, outermost_first_telescope.wf.t n C -> telescope.wf.t n (from_outer C).
    Proof.
      unfold from_outer.
      induction C; intros.
      - auto.
      - simpl in H. break_let; break_and. simpl.
        apply telescope.wf.app; simpl.
        apply IHC. auto.
        rewrite <- plus_n_O. auto.
    Qed.
  End wf.
End telescope.

Module sequent.
  Record t E : Type :=
    Make {
        context : telescope.t E;
        goal : E
    }.

  Module notations.
    Notation "H >> C" := (Make H C) (at level 81, right associativity) : sequent_scope.
    Bind Scope sequent_scope with sequent.t.
    Delimit Scope sequent_scope with sequent.
  End notations.

  Module wf.
    Import notations.
    Local Open Scope sequent.
    Definition t (S : sequent.t expr.t) : Prop :=
      match S with
      | H >> C => telescope.wf.t 0 H /\ expr.wf.t (length H) C
      end.
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
  | Fst_Eq (B : expr.t) (D : t) : t
  | Snd_Eq (i : nat) (sig_ty : expr.t) (D_a D_B : t) : t

  | Unit_Eq : t
  | tt_Eq : t
  | Unit_Intro : t

  | Eq_Eq (D_ty D_lhs D_rhs : t) : t
  | Eq_Mem_Eq : t -> t
  | Eq_Sym : t -> t
  | Eq_Subst (i : nat) (a : expr.t) (D_ty : t) (D_eq D_body : t) : t

  | Ceq_Eq (D_lhs D_rhs : t) : t
  | Ceq_Mem_Eq (D : t) : t
  | Ceq_Sym (D : t) : t
  | Ceq_Subst (e : expr.t) (D_ceq D_C : t) : t
  | Ceq_Step (D : t) : t
  | Ceq_Refl : t

  | Uni_Eq : t
  | Cumulative : t -> t

  | Witness (w : expr.t) : t -> t

  | Cut (g : guid.t) : t -> t

  | Var (x : nat) : t
  | Var_Eq : t
  .

  Module wf.
    Fixpoint t (n : nat) (D : t) : Prop :=
      match D with
      | derivation.Pi_Eq D_A D_B =>
        t n D_A /\ t (S n) D_B
      | derivation.Pi_Intro i D_A D_B =>
        t n D_A /\ t (S n) D_B
      | derivation.Pi_Elim x a D_A D_B =>
        x < n /\ expr.wf.t n a /\ t n D_A /\ t (S n) D_B
      | derivation.Lam_Eq i D_A D_B =>
        t n D_A /\ t (S n) D_B
      | derivation.Ap_Eq i pi_ty D_fun D_arg D_cod =>
        expr.wf.t n pi_ty /\ t n D_fun /\ t n D_arg /\ t n D_cod
      | derivation.Fun_Ext D_lhs D_rhs D =>
        t n D_lhs /\ t n D_rhs /\ t (S n) D
      | derivation.Sig_Eq D_A D_B =>
        t n D_A /\ t (S n) D_B
      | derivation.Sig_Intro i a D_A D_B D_eq =>
        expr.wf.t n a /\ t n D_A /\ t n D_B /\ t (S n) D_eq
      | derivation.Sig_Elim H D_C =>
        H < n /\ t (S (S n)) D_C
      | derivation.Pair_Eq i D_A D_B D_ty =>
        t n D_A /\ t n D_B /\ t (S n) D_ty
      | derivation.Fst_Eq B D =>
        expr.wf.t (S n) B /\ t n D
      | derivation.Snd_Eq i sig_ty D_a D_B =>
        expr.wf.t n sig_ty /\ t n D_a /\ t n D_B
      | derivation.Unit_Eq => True
      | derivation.tt_Eq => True
      | derivation.Unit_Intro => True
      | derivation.Eq_Eq D_ty D_lhs D_rhs =>
        t n D_ty /\ t n D_lhs /\ t n D_rhs
      | derivation.Eq_Mem_Eq D => t n D
      | derivation.Eq_Sym D => t n D
      | derivation.Eq_Subst i a D_ty D_eq D_body => False (* TODO *)
      | derivation.Ceq_Eq D_lhs D_rhs => t n D_lhs /\ t n D_rhs
      | derivation.Ceq_Mem_Eq D => t n D
      | derivation.Ceq_Sym D => t n D
      | derivation.Ceq_Subst e D_ceq D_C => expr.wf.t (S n) e /\ t n D_ceq /\ t n D_C
      | derivation.Ceq_Step D => t n D
      | derivation.Ceq_Refl => True
      | derivation.Uni_Eq => True
      | derivation.Cumulative D => t n D
      | derivation.Witness w D => expr.wf.t n w /\ t n D
      | derivation.Cut g D => t (S n) D
      | derivation.Var x => x < n
      | derivation.Var_Eq => True
      end.
    End wf.
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
    | derivation.Eq_Subst i a D_ty D_eq D_body => expr.tt
    | derivation.Ceq_Eq D_lhs D_rhs => expr.tt
    | derivation.Ceq_Mem_Eq D => expr.tt
    | derivation.Ceq_Sym D => expr.tt
    | derivation.Ceq_Subst e D_ceq D_C => f D_C
    | derivation.Ceq_Step D => expr.tt
    | derivation.Ceq_Refl => expr.tt
    | derivation.Uni_Eq => expr.tt
    | derivation.Cumulative D => expr.tt
    | derivation.Witness w D => w
    | derivation.Cut g D =>
      expr.subst (f D) 0 (expr.Cust g)
    | derivation.Var x => expr.Var x
    | derivation.Var_Eq => expr.tt
    end.

  Lemma wf : forall D n, derivation.wf.t n D -> expr.wf.t n (f D).
  Proof.
    induction D; simpl; intuition.
    - apply expr.wf.subst; intuition auto with arith.
      simpl. intuition.
    - apply expr.wf.subst; intuition auto with arith.
      apply expr.wf.subst; intuition auto with arith.
      simpl. intuition.
    - apply expr.wf.subst; intuition auto with arith.
      simpl. intuition.
  Qed.
End extract.

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

  Definition unwrap {A R} (x : option A) : tactic_monad.t R A :=
    match x with
    | Some a => tactic_monad.ret a
    | None => tactic_monad.fail
    end.

  Ltac unfold_tactic_monad :=
    unfold unwrap, assume_so, assume_sb, run, ap, map, bind, ret in *.

  Module notations.
  Notation "m >>= f" := (bind m f) (at level 81, right associativity) : tactic_monad.
  Notation "m1 >> m2" := (bind m1 (fun _ => m2)) (at level 81, right associativity) : tactic_monad.

  Notation "x <- m ;; f" := (bind m (fun x => f)) (at level 81, right associativity) : tactic_monad.
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

  Module wf.
    Definition t {D G} (P : G -> D -> Prop) g0 (r : t D G) : Prop :=
      forall ds, List.Forall2 (fun d g => P g d) ds (goals r) ->
            exists d, evidence r ds = Some d /\ P g0 d.
  End wf.
End tactic_result.

Module Type TACTIC.
  Parameter derivation goal : Type.

  Definition result := tactic_result.t derivation goal.

  Definition t := forall R, goal -> tactic_monad.t R result.
End TACTIC.

Module tactic <: TACTIC.
  Definition derivation := derivation.t.
  Definition goal := sequent.t expr.t.

  Definition result := tactic_result.t derivation goal.

  Definition t := forall R, goal -> tactic_monad.t R result.
End tactic.

Module refiner.
  Module result.
    Inductive t :=
    | Proved : derivation.t -> (* extract: *) expr.t -> t
    | Incomplete : list (sequent.t expr.t) -> t
    | Failed : t
    .
  End result.

  Definition prove (thm : expr.t) (t : tactic.t) : result.t :=
    match tactic_monad.run (t _ (sequent.Make [] thm)) with
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

Module primitive_tactics (T : TACTIC).
  Import tactic_monad.

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

  Definition join_evidence (subresults : list T.result) (ds : list T.derivation)
    : option (list T.derivation) :=
    let derivChunks :=
          chunk (List.map (fun x => List.length (x.(tactic_result.goals))) subresults) ds in
    match zipAppOpt (List.map (fun x => x.(tactic_result.evidence)) subresults) derivChunks with
    | None => None
    | Some x => sequence_option x
    end.

  Local Open Scope tactic_monad.

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


Fixpoint inc_digits (base : nat) (l : list nat) : list nat :=
  match l with
  | [] => [1]
  | d :: l => if base =? (S d) then 0 :: inc_digits base l
             else S d :: l
  end.

Fixpoint digits' (base : nat) (acc : list nat) (n : nat) : list nat :=
  match n with
  | 0 => acc
  | S n => digits' base (inc_digits base acc) n
  end.

Definition digits (base : nat) (n : nat) : list nat := List.rev (digits' base [0] n).

Definition decimal_digit_to_ascii (d : nat) : Ascii.ascii :=
  Ascii.ascii_of_nat (48 + d).

Definition ascii_to_decimal_digit (a : Ascii.ascii) : nat :=
  Ascii.nat_of_ascii a - 48.

Definition is_digit (a : Ascii.ascii) : bool := false.


Fixpoint string_to_list s :=
  match s with
  | String.EmptyString => nil
  | String.String c s' => c :: (string_to_list s')
  end.

Fixpoint list_to_string l :=
  match l with
  | nil => String.EmptyString
  | h::l' => String.String h (list_to_string l')
  end.

Definition nat_to_string (n : nat) : String.string :=
  list_to_string (List.map decimal_digit_to_ascii (digits 10 n)).

(*
Fixpoint from_digits (base : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | d :: l => base * from_digits base l + d
  end.

Definition nat_from_string (s : String.string) : nat :=
  from_digits 10 (List.rev (List.map ascii_to_decimal_digit (string_to_list s))).

Lemma string_to_list_to_string :
  forall s, list_to_string (string_to_list s) = s.
Proof.
  induction s; auto; simpl.
  now rewrite IHs.
Qed.

Lemma list_to_string_to_list :
  forall l, string_to_list (list_to_string l) = l.
Proof.
  induction l; auto; simpl.
  now rewrite IHl.
Qed.

Fixpoint max_suffix (acc : nat) (base : String.string) (l : list String.string) : nat :=
  match l with
  | [] => acc
  | s :: l =>
    max_suffix
      (if String.prefix base s
       then if String.string_dec base s then 1
            else max (S (S (nat_from_string (String.substring (String.length base) (String.length s) s)))) acc
       else acc)
      base
      l
  end.
Open Scope string_scope.
Eval compute in max_suffix 0 "x" ["xy"].


Definition fresh (base : String.string) (l : list String.string) : String.string.
*)

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

  | Ceq : t -> t -> t

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
    Notation "A = B 'in' C" := (ast.Eq A B C) (at level 70, B at next level) : ast_scope.

    Notation "A ~ B" := (ast.Ceq A B) (at level 70) : ast_scope.

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
    Check (\ "x", "x") ~ (\ "x", "x").
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
    | Ceq a1 a2 =>
      match to_expr' l a1 with None => None
      | Some a1 =>
      match to_expr' l a2 with None => None
      | Some a2 => Some (expr.Ceq a1 a2)
      end end
    | Uni i => Some (expr.Uni i)
    | Cust g => Some (expr.Cust g)
    end.

  Fixpoint to_expr (a : t) : option expr.t :=
    to_expr' [] a.

  Fixpoint from_expr' (l : list String.string) (e : expr.t) : option ast.t :=
    let fresh l := String.append "_" (String.append "x" (nat_to_string (length l))) in
    match e with
    | expr.Var n =>
      match nth_error l n with
      | Some s => Some (Var s)
      | None => None
      end
    | expr.Lam e =>
      match from_expr' (fresh l :: l) e with None => None
      | Some a => Some (Lam (fresh l) a)
      end
    | expr.App e1 e2 =>
      match from_expr' l e1 with None => None
      | Some a1 =>
      match from_expr' l e2 with None => None
      | Some a2 => Some (App a1 a2)
      end end
    | expr.Pi e1 e2 =>
      match from_expr' l e1 with None => None
      | Some a1 =>
      match from_expr' (fresh l :: l) e2 with None => None
      | Some a2 => Some (Pi (fresh l) a1 a2)
      end end
    | expr.Pair e1 e2 =>
      match from_expr' l e1 with None => None
      | Some a1 =>
      match from_expr' l e2 with None => None
      | Some a2 => Some (Pair a1 a2)
      end end
    | expr.Fst e =>
      match from_expr' l e with None => None
      | Some a => Some (Fst a)
      end
    | expr.Snd e =>
      match from_expr' l e with None => None
      | Some a => Some (Snd a)
      end
    | expr.Sig e1 e2 =>
      match from_expr' l e1 with None => None
      | Some a1 =>
      match from_expr' (fresh l :: l) e2 with None => None
      | Some a2 => Some (Sig (fresh l) a1 a2)
      end end
    | expr.tt => Some tt
    | expr.Unit => Some Unit
    | expr.Eq e1 e2 e3 =>
      match from_expr' l e1 with None => None
      | Some a1 =>
      match from_expr' l e2 with None => None
      | Some a2 =>
      match from_expr' l e3 with None => None
      | Some a3 => Some (Eq a1 a2 a3)
      end end end
    | expr.Ceq e1 e2 =>
      match from_expr' l e1 with None => None
      | Some a1 =>
      match from_expr' l e2 with None => None
      | Some a2 => Some (Ceq a1 a2)
      end end
    | expr.Uni i => Some (Uni i)
    | expr.Cust g => Some (Cust g)
    end.

  Definition from_expr e := from_expr' [] e.
End ast.

Module rules.
  Import P.
  Import tactic_monad.
  Local Open Scope tactic_monad.

  Import sequent.notations.
  Local Open Scope sequent.

  Open Scope string_scope.

  Definition nullary_derivation (d : derivation.t) :=
    tactic_result.Make(G:=sequent.t expr.t) (fun _ => Some d) [].

  Definition unary_derivation (d : derivation.t -> derivation.t) g :=
    tactic_result.Make(G:=sequent.t expr.t) (fun l => match l with
                                            | [x]  => Some (d x)
                                            | _ => None
                                            end) [g].

  Definition binary_derivation (d : derivation.t -> derivation.t -> derivation.t) g1 g2 :=
    tactic_result.Make(G:=sequent.t expr.t)
      (fun l => match l with
             | [d1; d2] => Some (d d1 d2)
             | _ => None
             end)
      [g1; g2].

  Definition ternary_derivation (d : derivation.t -> derivation.t ->
                                     derivation.t -> derivation.t) g1 g2 g3 :=
    tactic_result.Make(G:=sequent.t expr.t)
      (fun l => match l with
             | [d1; d2; d3] => Some (d d1 d2 d3)
             | _ => None
             end)
      [g1; g2; g3].

  Module wf.
    Definition t (rule : tactic.t) : Prop :=
      forall g res,
        sequent.wf.t g ->
        run (rule _ g) = Some res ->
        tactic_result.wf.t (fun g d => derivation.wf.t (length (sequent.context g)) d) g res /\
        List.Forall sequent.wf.t (tactic_result.goals res).
  End wf.

  Ltac head_symbol e :=
    match e with
    | ?f ?x => head_symbol f
    | _ => e
    end.

  Ltac crush_wf :=
    match goal with
    | [ |- wf.t ?f ] => let x := head_symbol f in unfold x
    end;
    unfold wf.t;
    intros;
    unfold_tactic_monad;
    repeat break_match; try discriminate;
    find_inversion;
    unfold nullary_derivation, unary_derivation, binary_derivation, ternary_derivation;
    simpl in *; repeat break_and; split; [
      unfold tactic_result.wf.t; simpl; intros;
      repeat match goal with
             | [ H : Forall2 _ _ _ |- _ ] => invc H
             end;
      eexists; intuition eauto; simpl in *; intuition;
      eauto using telescope.nth_length
    | unfold sequent.wf.t in *;
      repeat (apply Forall_cons || apply Forall_nil); simpl; intuition;
      try match goal with
      | [ H : telescope.nth _ _ = Some _ |- expr.wf.t _ _ ] =>
        eapply telescope.wf.nth in H; [|solve[eauto]]; simpl in H; intuition
      end ];
    auto using expr.wf.subst with arith;
    try match goal with
    | [  |- expr.wf.t _ (expr.lift _ ?n _) ] =>
      solve [apply expr.wf.lift' with (d := n); auto]
    end.

  Module unit.
    (* H >> unit = unit in U(i) *)
    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> (expr.Eq expr.Unit expr.Unit (expr.Uni _)) =>
        ret (nullary_derivation derivation.Unit_Eq)
      | _ => fail
      end.

    Lemma Eq_wf : wf.t Eq.
    Proof. crush_wf. Qed.

    (* H >> unit *)
    Definition Intro : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Unit => ret (nullary_derivation derivation.Unit_Intro)
      | _ => fail
      end.

    Lemma Intro_wf : wf.t Intro.
    Proof. crush_wf. Qed.

    (* H >> tt = tt in unit *)
    Definition TTEq : tactic.t :=
      fun R g =>
      match g with
      | H >> (expr.Eq expr.tt expr.tt expr.Unit) =>
        ret (nullary_derivation derivation.tt_Eq)
      | _ => fail
      end.

    Lemma TTEq_wf : wf.t TTEq.
    Proof. crush_wf. Qed.
  End unit.

  Module pi.
    (* H >> x:A -> B = x:A' -> B' in U(i)
         H >> A = A' in U(i)
         H, x:A >> B = B' in U(i) *)
    Definition Eq x : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.Pi A B) (expr.Pi A' B') (expr.Uni i) =>
        ret (binary_derivation derivation.Pi_Eq
                (H >> (expr.Eq A A' (expr.Uni i)))
                ((x, A) :: H >> (expr.Eq B B' (expr.Uni i))))
      | _ => fail
      end.

    Lemma Eq_wf x : wf.t (Eq x).
    Proof. crush_wf. Qed.

    (* H >> x:A -> B
         H >> A = A in U(i)
         H, x:A >> B *)
    Definition Intro (i : nat) x : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Pi A B =>
        ret (binary_derivation (derivation.Pi_Intro i)
                (H >> expr.Eq A A (expr.Uni i))
                ((x, A) :: H >> B))
      | _ => fail
      end.

    Lemma Intro_wf i x : wf.t (Intro i x).
    Proof. crush_wf. Qed.

    (* H >> C
         H(n) = x:A -> B
         H >> e = e in A
         H, [e/x]B >> C
     *)
    Definition Elim (n : nat) (a : ast.t) x : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        e <- unwrap (ast.to_expr' (telescope.names H) a) ;;
        _ <- assume_sb (expr.wf.dec (length H) e) ;;
        ty <- unwrap (telescope.nth H n) ;;
        match ty with
        | expr.Pi A B =>
          ret (binary_derivation (derivation.Pi_Elim n e)
                  (H >> expr.Eq e e A)
                  ((x, expr.subst B 0 e) :: H >> expr.lift 0 1 C))
        | _ => fail
        end
      end.

    Lemma Elim_wf n e x : wf.t (Elim n e x).
    Proof. crush_wf. Qed.

    (* H >> \x.e = \x.e' in x:A -> B
         H >> A = A in U(i)
         H, x:A >> e = e' in B *)
    Definition LamEq (i : nat) x : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.Lam e) (expr.Lam e') (expr.Pi A B) =>
        ret (binary_derivation (derivation.Lam_Eq i)
                (H >> expr.Eq A A (expr.Uni i))
                ((x, A) :: H >> expr.Eq e e' B))
      | _ => fail
      end.

    Lemma LamEq_wf i x : wf.t (LamEq i x).
    Proof. crush_wf. Qed.

    (* H >> n1 m1 = n2 m2 in T
         H >> n1 = n2 in x:A -> B
         H >> m1 = m2 in A
         H >> [n1/x]B = T in U(i) *)
    Definition ApEq (i : nat) (ty_a : ast.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq (expr.App n1 m1) (expr.App n2 m2) T =>
        ty <- unwrap (ast.to_expr' (telescope.names H) ty_a) ;;
        _ <- assume_sb (expr.wf.dec (length H) ty) ;;
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

    Lemma ApEq_wf i ty : wf.t (ApEq i ty).
    Proof. crush_wf. Qed.

    (* H >> e1 = e2 in x:A -> B
           H >> e1 = e1 in x:A -> B
           H >> e2 = e2 in x:A -> B
           H, x:A >> e1 x = e2 x in B *)
    Definition FunExt x : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Eq e1 e2 (expr.Pi A B) =>
        ret (ternary_derivation derivation.Fun_Ext
                (H >> expr.Eq e1 e1 (expr.Pi A B))
                (H >> expr.Eq e2 e2 (expr.Pi A B))
                ((x, A) :: H >> expr.Eq (expr.App (expr.lift 0 1 e1) (expr.Var 0))
                                   (expr.App (expr.lift 0 1 e2) (expr.Var 0))
                                   B))

      | _ => fail
      end.

    Lemma FunExt_wf x : wf.t (FunExt x).
    Proof. crush_wf. Qed.
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

    Lemma Eq_wf : wf.t Eq.
    Proof. crush_wf. Qed.


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

    Lemma Cumulative_Eq : wf.t Cumulative.
    Proof. crush_wf. Qed.
  End uni.

  Import expr.exports.
  Import expr.notations.
  Local Open Scope expr.

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

    Lemma Hyp_wf n : wf.t (Hyp n).
    Proof. crush_wf. Qed.

    (* H >> x = x in A
         H(x) = A *)
    Definition HypEq : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Var n1 = expr.Var n2 in A =>
        _ <- assume_sb (Nat.eq_dec n1 n2) ;;
        ty <- unwrap (telescope.nth H n1) ;;
        _ <- assume_sb (expr.eq_dec A ty) ;;
        ret (nullary_derivation derivation.Var_Eq)
      | _ => fail
      end.

    Lemma HypEq_wf : wf.t HypEq.
    Proof. crush_wf. Qed.

    Definition Witness (a : ast.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        e <- unwrap (ast.to_expr' (telescope.names H) a) ;;
        _ <- assume_sb (expr.wf.dec (length H) e) ;;
        ret (unary_derivation (derivation.Witness e)
              (H >> e = e in C))
      end.

    Lemma Witness_wf a : wf.t (Witness a).
    Proof. crush_wf. Qed.

    Definition Compute (n : nat) : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        C' <- unwrap (run.f n C) ;;
        ret (unary_derivation (fun x => x)
              (H >> C'))
      end.

    Lemma Compute_wf n : wf.t (Compute n).
    Proof. crush_wf. Admitted.
  End general.

  Module eq.
    (* H >>   m1 = n1 in A1   =   m2 = n2 in A2   in U(i)
           H >> A1 = A2 in U(i)
           H >> m1 = m2 in A1
           H >> n1 = n2 in A1 *)
    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> (m1 = n1 in A1) = (m2 = n2 in A2) in expr.Uni i =>
        ret (ternary_derivation derivation.Eq_Eq
                (H >> A1 = A2 in expr.Uni i)
                (H >> m1 = m2 in A1)
                (H >> n1 = n2 in A1))
      | _ => fail
      end.

    Lemma Eq_wf : wf.t Eq.
    Proof. crush_wf. Qed.
  End eq.

  Module sig.
    (* H >> x:A * B = x:A' * B' in U(i)
           H >> A = A' in U(i)
           H, x:A >> B = B' in U(i) *)
    Definition Eq (x : String.string) : tactic.t :=
      fun R g =>
      match g with
      | H >>  A * B = A' * B' in expr.Uni i =>
        ret (binary_derivation derivation.Sig_Eq
               (H >> A = A' in expr.Uni i)
               ((x, A)%core :: H >> B = B' in expr.Uni i))
      | _ => fail
      end.

    Lemma Eq_wf x : wf.t (Eq x).
    Proof. crush_wf. Qed.

    (* H >> x:A * B
         H >> a = a in A
         H >> [a/x]B
         H, x:A >> B = B in U(i) *)
    Definition Intro (i : nat) (a : ast.t) x : tactic.t :=
      fun R g =>
      match g with
      | H >> A * B =>
        e <- unwrap (ast.to_expr' (telescope.names H) a) ;;
        _ <- assume_sb (expr.wf.dec (length H) e) ;;
        ret (ternary_derivation (derivation.Sig_Intro i e)
                (H >> e = e in A)
                (H >> expr.subst B 0 e)
                ((x,A)%core :: H >> B = B in Uni i))
      | _ => fail
      end.

    Lemma Intro_wf i a x : wf.t (Intro i a x).
    Proof. crush_wf. Qed.

    (* H >> C
         H(n) = x:A * B
         H, x:A, B >> C *)
    Definition Elim (n : nat) x y : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        ty <- unwrap (telescope.nth H n) ;;
        match ty with
        | A * B =>
          ret (unary_derivation (derivation.Sig_Elim n)
                ((y,B) :: (x,A) :: H >> expr.lift 0 2 C)%core)
        | _ => fail
        end
      end.

    Lemma Elim_wf n x y : wf.t (Elim n x y ).
    Proof. crush_wf. Qed.

    (* H1, z : x:A * B, H2 >> C
         H1, z : x:A * B, a:A, b:[a/x]B, [(a,b)/z]H2 >> [(a,b)/z] C *)
    Definition Elim' (a : ast.t) x y : tactic.t :=
      fun R g =>
      match g with
      | H >> C =>
        e <- unwrap (ast.to_expr' (telescope.names H) a);;
        match e with
        | expr.Var n =>
          ty <- unwrap (telescope.nth H n) ;;
          match telescope.split H n with
          | Some (H1, (_, A * B), H2)%core =>
            let H1 := telescope.lift (S n) 2 H1 in
            let C := expr.lift (S n) 2 C in
            let H := telescope.subst H1 n (S n, n) ++ (y,B) :: (x,A) :: H2 in
            let C := expr.subst C n (S n, n) in

            ret (unary_derivation (derivation.Sig_Elim n)
                  (H >> C))
          | _ => fail
          end%core
        | _ => fail
        end
      end.

(*
          ret (unary_derivation (derivation.Sig_Elim n)
                (B :: A :: H1 >> expr.lift (length H1) 2 C)) *)

    Lemma Elim'_wf n x y : wf.t (Elim' n x y).
    Proof. crush_wf. Admitted.

    (* H >> (a,b) = (a',b') in x:A * B
         H >> a = a' in A
         H >> b = b' in [a/x]B
         H, x:A >> B = B in U(i) *)
    Definition PairEq (i : nat) x : tactic.t :=
      fun R g =>
      match g with
      | H >> (a,b) = (a',b') in A * B =>
        ret (ternary_derivation (derivation.Pair_Eq i)
                (H >> a = a' in A)
                (H >> b = b' in expr.subst B 0 a)
                ((x,A)%core :: H >> B = B in Uni i))
      | _ => fail
      end.

    Lemma PairEq_wf i x : wf.t (PairEq i x).
    Proof. crush_wf. Qed.

    (* H >> fst m1 = fst m2 in A
         H >> m1 = m2 in A * B
     *)
    Definition FstEq (B_a : ast.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Fst m1 = expr.Fst m2 in A =>
        B <- unwrap (ast.to_expr' (telescope.names H) B_a) ;;
        _ <- assume_sb (expr.wf.dec (S (length H)) B) ;;
        ret (unary_derivation (derivation.Fst_Eq B)
                (H >> m1 = m2 in A * B))
      | _ => fail
      end.

    Lemma FstEq_wf B : wf.t (FstEq B).
    Proof. crush_wf. Qed.

    (* H >> snd m1 = snd m2 in C
         H >> m1 = m2 in x:A * B
         H >> [fst m1/x]B = C in U(i) *)
    Definition SndEq (i : nat) (ty_a : ast.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.Snd m1 = expr.Snd m2 in C =>
        ty <- unwrap (ast.to_expr' (telescope.names H) ty_a) ;;
        _ <- assume_sb (expr.wf.dec (length H) ty) ;;
        match ty with
        | A * B =>
          ret (binary_derivation (derivation.Snd_Eq i ty)
                 (H >> m1 = m2 in A * B)
                 (H >> expr.subst B 0 (Fst m1) = C in Uni i))
        | _ => fail
        end
      | _ => fail
      end.

    Lemma SndEq_wf i ty : wf.t (SndEq i ty).
    Proof. crush_wf. Qed.
  End sig.

  Module ceq.
    (* H >> a ~ a *)
    Definition Refl : tactic.t :=
      fun R g =>
      match g with
      | H >> e1 ~ e2 =>
        _ <- assume_sb (expr.eq_dec e1 e2) ;;
        ret (nullary_derivation derivation.Ceq_Refl)
      | _ => fail
      end.

    Lemma Refl_wf : wf.t Refl.
    Proof. crush_wf. Qed.

    Definition Sym : tactic.t :=
      fun R g =>
      match g with
      | H >> e1 ~ e2 =>
        ret (unary_derivation derivation.Ceq_Sym
              (H >> e2 ~ e1))
      | _ => fail
      end.

    Lemma Sym_wf : wf.t Sym.
    Proof. crush_wf. Qed.

    Definition Mem_Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> expr.tt = expr.tt in (e1 ~ e2) =>
        ret (unary_derivation derivation.Ceq_Mem_Eq
              (H >> e1 ~ e2))
      | _ => fail
      end.

    Lemma Mem_Eq_wf : wf.t Mem_Eq.
    Proof. crush_wf. Qed.

    Definition Eq : tactic.t :=
      fun R g =>
      match g with
      | H >> (e1 ~ e2) = (e3 ~ e4) in expr.Uni i =>
        ret (binary_derivation derivation.Ceq_Eq
              (H >> e1 ~ e3)
              (H >> e2 ~ e4))
      | _ => fail
      end.

    Lemma Eq_wf : wf.t Eq.
    Proof. crush_wf. Qed.

    Definition Step : tactic.t :=
      fun R g =>
      match g with
      | H >> e1 ~ e2 =>
        match step.f e1 with
        | step.result.Step e1' =>
          ret (unary_derivation derivation.Ceq_Step
                (H >> e1' ~ e2))
        | _ => fail
        end
      | _ => fail
      end.

    Lemma Step_wf : wf.t Step.
    Proof. crush_wf. Admitted.

    Definition Subst (x : String.string) (ty_a : ast.t) (C_a : ast.t) : tactic.t :=
      fun R g =>
      match g with
      | H >> Ca =>
        ty <- unwrap (ast.to_expr' (telescope.names H) ty_a) ;;
        _ <- assume_sb (expr.wf.dec (length H) ty) ;;

        match ty with
        | a ~ b =>
          C <- unwrap (ast.to_expr' (x :: telescope.names H) C_a) ;;
          _ <- assume_sb (expr.wf.dec (S (length H)) C) ;;
          _ <- assume_sb (expr.eq_dec Ca (expr.subst C 0 a)) ;;
          ret (binary_derivation (derivation.Ceq_Subst C)
                 (H >> a ~ b)
                 (H >> expr.subst C 0 b))
        | _ => fail
        end
      end.

    Lemma Subst_wf x ty_a C_a : wf.t (Subst x ty_a C_a).
    Proof. crush_wf. Qed.
  End ceq.
End rules.
Import rules.

(* We can use our rules to prove stuff! *)
Eval compute in refiner.prove (expr.Eq expr.Unit expr.Unit (expr.Uni 0)) rules.unit.Eq.
Eval compute in refiner.prove expr.Unit rules.unit.Intro.
Eval compute in refiner.prove (expr.Eq expr.tt expr.tt expr.Unit) rules.unit.TTEq.

Fixpoint unparse_telescope' (l : list String.string) (C : outermost_first_telescope.t expr.t) : option (outermost_first_telescope.t ast.t) :=
  match C with
  | [] => Some []
  | (n,e) :: C =>
    match ast.from_expr' l e with
    | None => None
    | Some a =>
      match unparse_telescope' (n :: l) C with
      | None => None
      | Some C => Some ((n, a) :: C)
      end
    end
  end.

Definition unparse_sequent (s : sequent.t expr.t) : option (sequent.t ast.t) :=
  match s with
  | sequent.Make H C =>
    match unparse_telescope' [] (telescope.to_outer H) with
    | None => None
    | Some H' =>
      match ast.from_expr' (telescope.names H) C with
      | None => None
      | Some C => Some (sequent.Make H' C)
      end
    end
  end.

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

Eval compute in ast.from_expr funext.

(* A few simple notations for the tactics. *)
Notation "t ;; l" := (P.split t l) (at level 50, left associativity).
Notation "t1 ;;; t2" := (P.next t1 t2) (at level 50, left associativity).
Notation "t1 || t2" := (P.choose t1 t2).

Module tac_info.
  Record t :=
    Make {
        i : option nat;
        a : option ast.t;
        ns : list String.string
      }.

  Definition empty : t := Make None None [].
  Definition level (i : nat) : t := Make (Some i) None [].
  Definition arg (a : ast.t) : t := Make None (Some a) [].
  Definition names l : t := Make None None l.

  Definition get_i (x : t) {R} : tactic_monad.t R nat :=
    tactic_monad.unwrap (i x).

  Definition get_a (x : t) {R} : tactic_monad.t R ast.t :=
    tactic_monad.unwrap (a x).

  Definition get_ith_name' (x : t) (i : nat) {R} : tactic_monad.t R String.string :=
    tactic_monad.unwrap (nth_error (ns x) i).

  Definition get_ith_name (x : t) (i : nat) {R} : tactic_monad.t R String.string :=
    tactic_monad.choose [fun _ => get_ith_name' x i; fun _ => tactic_monad.ret "x"].

  Definition get_name (x : t) {R} := get_ith_name(R := R) x 0.
End tac_info.

Module tac.
  Definition Intro (info : tac_info.t) : tactic.t.
    refine (fun R g => _).
    refine (tactic_monad.choose
              [fun _ => unit.Intro g;
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i =>
                     tactic_monad.bind (tac_info.get_name info) (fun x =>
                     pi.Intro i x g));
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i =>
                     tactic_monad.bind (tac_info.get_a info) (fun e =>
                     tactic_monad.bind (tac_info.get_name info) (fun x =>
                     sig.Intro i e x g)))]).
  Defined.

  Definition Eq (info : tac_info.t) : tactic.t.
    refine (fun R g => _).
    refine (tactic_monad.choose
              [fun _ => unit.Eq g;
               fun _ => tactic_monad.bind (tac_info.get_name info) (fun x => pi.Eq x g);
               fun _ => tactic_monad.bind (tac_info.get_name info) (fun x => sig.Eq x g);
               fun _ => uni.Eq g;
               fun _ => eq.Eq g;
               fun _ => unit.TTEq g;
               fun _ => general.HypEq g;
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i =>
                     tactic_monad.bind (tac_info.get_name info) (fun x =>
                     pi.LamEq i x g));
               fun _ => tactic_monad.bind (tac_info.get_i info) (fun i =>
                     tactic_monad.bind (tac_info.get_name info) (fun x =>
                     sig.PairEq i x g))
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

Definition goggles (r : refiner.result.t) : option (list (sequent.t ast.t)) :=
  match r with
  | refiner.result.Incomplete l =>
    sequence_option (List.map unparse_sequent l)
  | _ => None
  end.


Import sequent.notations.
Open Scope sequent.
Open Scope ast.

(* Let's prove function extensionality! *)
Eval cbv in
  let go_eq := P.repeat 10 (tac.Eq tac_info.empty) in
  refiner.prove funext
                (pi.Intro 1 "A" ;;; go_eq ;;;
                 pi.Intro 1 "B" ;;; go_eq ;;;
                 pi.Intro 0 "f" ;;; go_eq ;;;
                 pi.Intro 0 "g" ;;; go_eq ;;;
                 pi.Intro 0 "H" ;;; go_eq ;; [
                     pi.ApEq 0 ("A" -> "B");;; go_eq;
                     pi.ApEq 0 ("A" -> "B");;; go_eq;
                     pi.FunExt "x";;; go_eq ;;;
                     pi.Elim 1 "x" "Hx";;; go_eq ;;;
                     tac.Assumption]).

Definition ast_proj1 : ast.t :=
  {"A" : Uni 0} ->
  {"B" : "A" -> Uni 0} ->
  ({"x" : "A"} * "B" "x") ->
  "A".

Definition proj1 : expr.t := ltac:(parse ast_proj1).

Eval cbv in
  let go_eq := P.repeat 10 (tac.Eq tac_info.empty) in
  refiner.prove proj1
  (pi.Intro 1 "A" ;;; go_eq ;;;
   pi.Intro 1 "B" ;; [go_eq ;;; uni.Cumulative;;; general.HypEq; P.id] ;;;
   pi.Intro 0 "p" ;; [go_eq ;;; pi.ApEq 1 ("A" -> Uni 0);;; go_eq; P.id] ;;;
   sig.Elim 0 "a" "b" ;;;
   general.Witness "a" ;;; go_eq).

Definition ast_snd_eq : ast.t :=
  Snd (tt, tt) = Snd (tt, tt) in Unit.

Definition snd_eq : expr.t := ltac:(parse ast_snd_eq).

Eval cbv in
  let go_eq := P.repeat 10 (tac.Eq tac_info.empty) in
    refiner.prove snd_eq
    (sig.SndEq 0 (Unit * Unit) ;;; go_eq ;;;
     sig.PairEq 0 "a" ;;; go_eq).


Definition ast_pair_eta : ast.t :=
  {"A" : Uni 0} ->
  {"B" : "A" -> Uni 0} ->
  {"z" : ({"x" : "A"} * "B" "x")} ->
  "z" = (Fst "z", Snd "z") in ({"x" : "A"} * "B" "x").

Definition pair_eta : expr.t := ltac:(parse ast_pair_eta).

Eval cbv in
  let go_eq := P.repeat 10 (tac.Eq tac_info.empty) in
  refiner.prove pair_eta
     (pi.Intro 1 "A" ;;; go_eq ;;;
      pi.Intro 1 "B" ;;; go_eq ;; [uni.Cumulative;;; go_eq ; P.id];;;
      pi.Intro 0 "z" ;;; go_eq ;; [pi.ApEq 1 ("A" -> Uni 0);;; go_eq; P.id];;;
      sig.Elim' "z" "a" "b" ;;;
      ceq.Subst "x" (Fst ("a", "b") ~ "a")
                (("a", "b") = ("x", Snd ("a", "b")) in {"_x4" : "A"}* "B" "_x4") ;;
      [ceq.Step;;; ceq.Refl; P.id];;;
      ceq.Subst "x" (Snd ("a", "b") ~ "b")
                (("a", "b") = ("a", "x") in {"_x4" : "A"}* "B" "_x4") ;;
      [ceq.Step;;; ceq.Refl; P.id];;;
      sig.PairEq 0 "y";;; go_eq ;;;
      pi.ApEq 1 ("A" -> Uni 0);;; go_eq).

(* End of main development. *)





(* Eventually we will support user-defined constants. For now, this is unused. *)
Module configuration.
  Module entry.
    Record t :=
      Make {
          type : expr.t;
          extract : expr.t
        }.
  End entry.

  Definition t := list (guid.t * entry.t).

  Definition empty : t := []%list.

  Definition insert (name : guid.t) (type : expr.t) (extract : expr.t) (C : t) : t :=
    assoc_set guid.eq_dec C name (entry.Make type extract).

  Definition type_of (name : guid.t) (C : t) : option (expr.t) :=
    option_map entry.type (assoc guid.eq_dec C name).

  Definition extract_of (name : guid.t) (C : t) : option (expr.t) :=
    option_map entry.extract (assoc guid.eq_dec C name).
End configuration.


(* Eventually we should give meaning to the proof theory in terms of the
   underlying computation system. Then we should be able to show that the
   rules above are sound. *)
