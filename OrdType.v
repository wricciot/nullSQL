Require Import Lists.List Sorted Bool Vector JMeq.

Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
Proof.
  rewrite H. reflexivity.
Qed.

Module Type OrdType.

  Parameter t : Type.

  Parameter lt : t -> t -> Prop.
  Parameter ltb : t -> t -> bool.

  Parameter eq_dec : forall (x y:t), {x = y} + {x <> y}.

  Parameter lt_norefl : forall x, ~ lt x x.
  Parameter lt_antisym : forall x y, lt x y -> lt y x -> False.
  Parameter lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

  Parameter linearity : forall x y, x = y \/ lt x y \/ lt y x.

  Parameter ltb_lt : forall x y, ltb x y = true <-> lt x y.

End OrdType.

Inductive vec_lt (A : Type) (ltA : A -> A -> Prop) : forall n, Vector.t A n -> Vector.t A n -> Prop :=
| vec_lt_hd  : forall n a b v w, ltA a b -> vec_lt A ltA (S n) (cons _ a _ v) (cons _ b _ w)
| vec_lt_tl  : forall n a v w, vec_lt A ltA n v w -> vec_lt A ltA (S n) (cons _ a _ v) (cons _ a _ w).

Definition vec_le (A : Type) (ltA : A -> A -> Prop) : forall n, Vector.t A n -> Vector.t A n -> Prop :=
  fun n v w => v = w \/ vec_lt A ltA n v w.

Definition vec_ltb (A : Type) (eq_decA : forall a b, {a = b} + {a <> b}) (ltbA : A -> A -> bool)
    n (v w : Vector.t A n) : bool :=
  Vector.fold_right2 (fun a b acc => if ltbA a b then true else if eq_decA a b then acc else false) false n v w.

Lemma vec_eq_dec (A : Type) (eq_decA : forall a b : A, {a = b} + {a <> b}) n (v w : Vector.t A n)
  : { v = w } + { v <> w }.
Proof.
  eapply (rect2 (fun n0 (v0 w0 : Vector.t A n0) => { v0 = w0 } + { v0 <> w0 })).
  left; reflexivity.
  intros. destruct (eq_decA a b).
  rewrite e. destruct H.
  rewrite e0. left; reflexivity.
  right. intro; apply n1. enough (tl (cons A b n0 v1) = tl (cons A b n0 v2)). exact H0.
  rewrite H. reflexivity.
  right. intro; apply n1. injection H0; intuition.
Qed.

Definition vec_eqb (A : Type) (eq_decA : forall a b, {a = b} + {a <> b}) n (v w : Vector.t A n) : bool :=
  if vec_eq_dec A eq_decA n v w then true else false.

Definition projT1_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
  : projT1 u = projT1 v
  := f_equal (@projT1 _ _) p.

Definition projT2_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
  : @eq_rect _ _ _ (projT2 u) _ (projT1_eq p) = projT2 v.
Proof.
  rewrite p. reflexivity.
Qed.

Lemma f_JMeq : forall A (T : A -> Type) (f : forall a, T a) x y, x = y -> f x ~= f y.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Definition existT_projT2_eq {A} {P : A -> Type} a (p1 p2 :  P a) (e : existT _ _ p1 = existT _ _ p2)
  : p1 = p2.
Proof.
  transitivity (projT2 (existT P a p1)). reflexivity. 
  transitivity (projT2 (existT P a p2)). apply JMeq_eq. eapply (f_JMeq _ _ (@projT2 A P) _ _ e).
  reflexivity.
Qed.

Lemma vec_lt_norefl (A : Type) ltA (ltA_norefl : forall a, ~ ltA a a) n v : ~ vec_lt A ltA n v v.
Proof.
  induction v.
  intro. inversion H.
  intro. inversion H; intuition.
  pose (H3' := existT_projT2_eq _ _ _ H3); clearbody H3'; clear H3.
  pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
  subst. contradiction (ltA_norefl h).
  pose (H3' := existT_projT2_eq _ _ _ H3); clearbody H3'; clear H3.
  pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
  subst. apply IHv. exact H2.
Qed.

Lemma vec_lt_antisym (A : Type) (ltA : A -> A -> Prop) (ltA_norefl : forall a, ~ ltA a a)
  (ltA_antisym : forall a b, ltA a b -> ltA b a -> False) n v w
  : vec_lt A ltA n v w -> vec_lt A ltA n w v -> False.
Proof.
  intro. induction H.
  + intro. inversion H0.
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H6' := existT_projT2_eq _ _ _ H6); clearbody H6'; clear H6.
    subst. apply (ltA_antisym _ _ H H3).
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H6' := existT_projT2_eq _ _ _ H6); clearbody H6'; clear H6.
    subst. contradiction (ltA_norefl _ H).
  + intro. inversion H0.
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H6' := existT_projT2_eq _ _ _ H6); clearbody H6'; clear H6.
    subst. contradiction (ltA_norefl _ H3).
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
    subst. apply IHvec_lt. exact H3.
Qed.

Lemma vec_lt_trans (A : Type) (ltA : A -> A -> Prop) 
  (* 
  (ltA_norefl : forall a, ~ ltA a a)
  (ltA_antisym : forall a b, ltA a b -> ltA b a -> False) *)
  (ltA_trans : forall a b c, ltA a b -> ltA b c -> ltA a c) n u v w 
  : vec_lt A ltA n u v -> vec_lt A ltA n v w -> vec_lt A ltA n u w.
Proof.
  intro. induction H.
  + intro. inversion H0.
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
    subst. constructor. eapply ltA_trans. exact H. exact H3.
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
    subst. constructor. exact H.
  + intro. inversion H0.
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
    subst. constructor. exact H3.
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
    subst. constructor 2. apply IHvec_lt. exact H3.
Qed.

Lemma vec_linearity (A :Type) (ltA : A -> A -> Prop) (linA : forall a b, a = b \/ ltA a b \/ ltA b a) n u v
  : u = v \/ vec_lt A ltA n u v \/ vec_lt A ltA n v u.
Proof.
  eapply (rect2 (fun n0 (u0 v0 : Vector.t A n0) => u0 = v0 \/ vec_lt A ltA n0 u0 v0 \/ vec_lt A ltA n0 v0 u0)).
  + left. reflexivity.
  + intros. destruct (linA a b). 
    - rewrite H0. destruct H.
      * rewrite H. left. reflexivity.
      * right. destruct H.
        ++ left. constructor 2. exact H.
        ++ right. constructor 2. exact H.
    - right. destruct H0.
      * left. constructor. exact H0.
      * right. constructor. exact H0.
Qed.

Lemma vec_ltb_lt (A : Type) (ltA : A -> A -> Prop) (ltbA : A -> A -> bool)
  (eq_decA : forall (a b : A), {a = b} + {a <> b})
  (ltA_norefl : forall a, ~ ltA a a)
  (ltbA_ltA : forall a b, ltbA a b = true <-> ltA a b)
  n u v
  : vec_ltb A eq_decA ltbA n u v = true <-> vec_lt A ltA n u v.
Proof.
  eapply (rect2 (fun n0 (u0 v0 : Vector.t A n0) =>
    vec_ltb A eq_decA ltbA n0 u0 v0 = true <-> vec_lt A ltA n0 u0 v0)).
  + simpl. intuition. discriminate H. contradiction (vec_lt_norefl _ _ ltA_norefl _ _ H).
  + intros. simpl. destruct (ltbA a b) eqn:Hab; simpl; intuition.
    - constructor. apply ltbA_ltA. exact Hab.
    - destruct (eq_decA a b). rewrite e. constructor 2. apply H0. exact H. discriminate H.
    - destruct (eq_decA a b).
      * apply H1.
        rewrite e in H. inversion H. 
        ++ contradiction (ltA_norefl _ H4).
        ++ pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
           pose (H6' := existT_projT2_eq _ _ _ H6); clearbody H6'; clear H6. subst. exact H4.
      * inversion H.
        ++ rewrite (proj2 (ltbA_ltA _ _) H4) in Hab. discriminate Hab.
        ++ pose (H5' := existT_projT2_eq _ _ _ H5); clearbody H5'; clear H5.
           pose (H7' := existT_projT2_eq _ _ _ H7); clearbody H7'; clear H7. subst.
           contradiction f. reflexivity.
Qed.

Module Type OrdVecType.

  Parameter t : nat -> Type.

  Parameter vlt : forall n, t n -> t n -> Prop.
  Parameter vltb : forall n, t n -> t n -> bool.

  Parameter veq_dec : forall n (x y:t n), {x = y} + {x <> y}.

  Parameter vlt_norefl : forall n x, ~ vlt n x x.
  Parameter vlt_antisym : forall n x y, vlt n x y -> vlt n y x -> False.
  Parameter vlt_trans : forall n x y z, vlt n x y -> vlt n y z -> vlt n x z.

  Parameter vlinearity : forall n x y, x = y \/ vlt n x y \/ vlt n y x.

  Parameter vltb_vlt : forall n x y, vltb n x y = true <-> vlt n x y.

End OrdVecType.

Module OrdVec (O : OrdType) <: OrdVecType.

  Definition t := Vector.t O.t.

  Definition vlt := vec_lt O.t O.lt.
  Definition vltb := vec_ltb O.t O.eq_dec O.ltb.
  Definition veq_dec := vec_eq_dec O.t O.eq_dec.

  Definition vlt_norefl := vec_lt_norefl O.t O.lt O.lt_norefl.
  Definition vlt_antisym := vec_lt_antisym O.t O.lt O.lt_norefl O.lt_antisym.
  Definition vlt_trans := vec_lt_trans O.t O.lt O.lt_trans.

  Definition vlinearity := vec_linearity O.t O.lt O.linearity.

  Definition vltb_vlt := vec_ltb_lt O.t O.lt O.ltb O.eq_dec O.lt_norefl O.ltb_lt.

  Definition vle := fun n u v => vlt n u v \/ u = v.
  Definition vleb := fun n u v => if veq_dec n u v then true else vltb n u v.

  Lemma vle_refl : forall n u, vle n u u.
  Proof.
    intros; right; reflexivity.
  Qed.

  Lemma vle_antisym : forall n u v, vle n u v -> vle n v u -> u = v.
  Proof.
    intros. destruct H; intuition.
    destruct H0; intuition.
    contradiction (vlt_antisym _ _ _ H H0).
  Qed.

  Lemma vle_trans : forall n u v w, vle n u v -> vle n v w -> vle n u w.
  Proof.
    intros. destruct H; subst; auto. left. destruct H0; subst; auto.
    eapply vlt_trans; eassumption.
  Qed.

  Lemma vleb_vle : forall n u v, vleb n u v = true <-> vle n u v.
  Proof.
    intros. unfold vleb; split; intro.
    + destruct (veq_dec n u v).
      - right. exact e.
      - left. apply vltb_vlt. exact H.
    + destruct H.
      - destruct (veq_dec n u v); intuition. apply vltb_vlt. exact H.
      - destruct (veq_dec n u v); intuition.
  Qed.

  Lemma not_vle_to_vlt : forall n u v, ~ vle n u v -> vlt n v u.
  Proof.
    intros. destruct (vlinearity n u v).
    + rewrite H0 in H. contradiction H. right. reflexivity.
    + destruct H0.
      - contradiction H. left. exact H0.
      - exact H0.
  Qed.

  Lemma vleb_false_not_vle : forall n u v, vleb n u v = false <-> ~ vle n u v.
  Proof.
    intros. split; intro.
    + intro. rewrite (proj2 (vleb_vle _ _ _) H0) in H. discriminate H.
    + destruct (vleb n u v) eqn:e; intuition. contradiction H. apply vleb_vle. exact e.
  Qed.

End OrdVec.