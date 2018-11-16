(* Sort: Insertion sort *)

(** The insertion-sort program **)

Require Import Lists.List Bool OrdType.

Module InsertionSort (O : OrdType.OrdType).

  Import ListNotations.

  Module OV := OrdType.OrdVec O.

  Fixpoint le_list {n} x (l : list (OV.t n)) :=
    match l with
    | [] => true
    | y :: l' => (OV.vleb n x y) && le_list x l'
    end.

  Fixpoint is_sorted {n} (l : list (OV.t n)) :=
    match l with
    | [] => true
    | h :: l' => le_list h l' && is_sorted l'
    end.

  Fixpoint insert {n} (x: OV.t n) (l: list (OV.t n)) :=
    match l with
    | nil => x::nil
    | h::l' => if OV.vleb n x h then x::h::l' else h :: insert x l'
    end.

  Fixpoint sort {n} (l: list (OV.t n)) : list (OV.t n) :=
    match l with
    | nil => nil
    | h::l' => insert h (sort l')
    end.

  (** Specification of correctness **)
  Inductive sorted {n} : list (OV.t n) -> Prop :=
  | sorted_nil : sorted nil
  | sorted_1   : forall x,  sorted (x::nil)
  | sorted_cons: forall x y l, OV.vle n x y -> sorted (y::l) -> sorted (x::y::l).

  Hint Constructors sorted.

  Definition is_a_sorting_algorithm {n} (f: list (OV.t n) -> list (OV.t n)) :=
    forall al, (forall x, count_occ (OV.veq_dec n) al x = count_occ (OV.veq_dec n) (f al) x) /\ sorted (f al).

(** Proof of correctness **)

  Lemma insert_sorted {n} : forall a (l : list (OV.t n)), sorted l -> sorted (insert a l).
  Proof.
    intros.
    induction H.
    simpl. auto.

    simpl. destruct (OV.vleb n a x) eqn:e. constructor. apply OV.vleb_vle. exact e.
    constructor.
    constructor. left. apply OV.not_vle_to_vlt. apply OV.vleb_false_not_vle. exact e.

    constructor.

    simpl. destruct (OV.vleb n a x) eqn:e; intuition.
    constructor. apply OV.vleb_vle. exact e. intuition.
    destruct (OV.vleb n a y) eqn:e0; intuition.

    constructor. left. apply OV.not_vle_to_vlt. apply OV.vleb_false_not_vle. exact e.
    constructor. apply OV.vleb_vle. exact e0.
    exact H0.

    constructor. exact H.

    simpl in IHsorted. destruct (OV.vleb n a y) eqn:e1; intuition. discriminate e0.
  Qed.

  Theorem sort_sorted {n} : forall (l : list (OV.t n)), sorted (sort l).
  Proof.
    intros.
    induction l; simpl; auto.
    apply insert_sorted. assumption.
  Qed.

  Lemma le_le_list {n} a t (l : list (OV.t n)) : OV.vleb n a t = true -> le_list t l = true -> le_list a l = true.
  Proof.
    intro. elim l; intuition.
    simpl. simpl in H1. apply andb_true_iff; split.
    + apply OV.vleb_vle. apply (OV.vle_trans _ _ t). apply OV.vleb_vle. exact H.
      apply OV.vleb_vle. destruct (OV.vleb _ t a0); intuition.
    + apply H0. rewrite andb_comm in H1. destruct (le_list t l0); intuition.
  Qed.

  Lemma sorted_is_sorted {n} : forall (l : list (OV.t n)), is_sorted l = true <-> sorted l.
  Proof.
    intros. elim l.
    + intuition.
    + intros. simpl. destruct l0.
      - intuition.
      - split.
        * intro. constructor.
          ++ simpl in H0. apply OV.vleb_vle. destruct (OV.vleb _ a t); intuition.
          ++ apply H. rewrite andb_comm in H0. destruct (is_sorted (t::l0)); intuition.
        * intro. simpl. inversion H0. subst. apply andb_true_iff. split.
          ++ apply andb_true_iff. split.
            -- apply OV.vleb_vle. exact H3.
            -- apply (le_le_list _ t). apply OV.vleb_vle. exact H3.
               simpl in H. destruct (le_list t l0); intuition.
          ++ apply H. exact H5.
  Qed.

  Lemma sort_is_sorted {n} : forall (l : list (OV.t n)), is_sorted (sort l) = true.
  Proof.
    intros. apply sorted_is_sorted. apply sort_sorted.
  Qed.

  Lemma count_occ_insert_eq {n} x (bl : list (OV.t n)) :
    count_occ (OV.veq_dec n) (insert x bl) x = S (count_occ (OV.veq_dec n) bl x).
  Proof.
    elim bl; intuition.
    + simpl. destruct (OV.veq_dec _ x x); intuition.
    + simpl. destruct (OV.vleb _ x a); simpl; intuition.
      - destruct (OV.veq_dec _ x x); intuition.
      - destruct (OV.veq_dec _ a x); intuition.
  Qed.

  Lemma count_occ_insert_neq {n} x y (bl : list (OV.t n)) : x <> y ->
    count_occ (OV.veq_dec _) (insert x bl) y = count_occ (OV.veq_dec _) bl y.
  Proof.
    intro. elim bl; intuition.
    + simpl. destruct (OV.veq_dec _ x y); intuition.
    + simpl. destruct (OV.vleb _ x a); simpl; intuition.
      - destruct (OV.veq_dec _ x y); intuition.
      - destruct (OV.veq_dec _ a y); intuition.
  Qed.

  Lemma count_occ_insert {n} : forall (al bl : list (OV.t n)) x y, 
    count_occ (OV.veq_dec _) al x = count_occ (OV.veq_dec _) bl x ->
    count_occ (OV.veq_dec _) (y::al) x = count_occ (OV.veq_dec _) (insert y bl) x.
  Proof.
    intros. simpl. destruct (OV.veq_dec _ y x).
    - rewrite e. rewrite count_occ_insert_eq. rewrite H. reflexivity.
    - erewrite count_occ_insert_neq; auto.
  Qed.

  Lemma count_occ_sort {n} : forall al x, count_occ (OV.veq_dec n) al x = count_occ (OV.veq_dec n) (sort al) x.
  Proof.
    intros. elim al; intuition.
    simpl (sort (a::l)). apply count_occ_insert. apply H.
  Qed.

  Theorem insertion_sort_correct {n} :  is_a_sorting_algorithm (@sort n).
  Proof.
    split.
    + intro. apply count_occ_sort.
    + apply sort_sorted.
  Qed.

  Lemma lt_sorted_count_occ_O {n} a b l:
    OV.vlt n a b -> sorted (b::l) -> count_occ (OV.veq_dec n) (b::l) a = O.
  Proof.
    intros. generalize b H H0. clear b H H0. induction l; intros.
    + simpl. destruct (OV.veq_dec _ b a); intuition. 
      rewrite e in H. destruct (OV.vlt_norefl _ _ H).
    + inversion H0; intuition. simpl.
      destruct (OV.veq_dec _ b a); intuition.
      - rewrite e in H. destruct (OV.vlt_norefl _ _ H).
      - eapply (IHl a0).
        * destruct H3.
          ++ apply (OV.vlt_trans _ _ _ _ H). exact H3.
          ++ rewrite <- H3. exact H.
        * exact H5.
  Qed.

  Theorem ext_eq {n} (al bl : list (OV.t n)) : 
    sorted al -> sorted bl -> 
    (forall x, count_occ (OV.veq_dec n) al x = count_occ (OV.veq_dec _) bl x) ->
    al = bl.
  Proof.
    intros. generalize bl H0 H1. clear bl H0 H1. induction al; intros.

    destruct bl; intuition. absurd (count_occ (OV.veq_dec _) [] t = count_occ (OV.veq_dec _) (t::bl) t).
    simpl. destruct (OV.veq_dec _ t t); intuition. discriminate H2.
    apply H1.

    destruct bl; intuition. absurd (count_occ (OV.veq_dec _) (a::al) a = count_occ (OV.veq_dec _) [] a).
    simpl. destruct (OV.veq_dec _ a a); intuition. discriminate H2.
    apply H1.

    destruct (OV.vlinearity _ a t).
    + subst. f_equal. assert (sorted al). inversion H; intuition.
      assert (sorted bl). inversion H0; intuition.
      apply IHal; intuition.
      pose (H1' := H1 x); clearbody H1'. simpl in H1'. destruct (OV.veq_dec _ t x); intuition.
    + destruct H2.
      - absurd (count_occ (OV.veq_dec _) (a::al) a = count_occ (OV.veq_dec _) (t::bl) a).
        * (* doesn't work: looks like a Coq bug?
            rewrite (lt_sorted_count_occ_O _ _ _ H2 H0). *)
          replace (count_occ (OV.veq_dec n) (t :: bl) a) with 0. 
          simpl. destruct (OV.veq_dec _ a a); intuition. discriminate H3.
          symmetry. apply lt_sorted_count_occ_O. exact H2. exact H0.
        * apply H1.
      - absurd (count_occ (OV.veq_dec _) (a::al) t = count_occ (OV.veq_dec _) (t::bl) t).
        * replace (count_occ (OV.veq_dec n) (a :: al) t) with 0. simpl.
          destruct (OV.veq_dec _ t t); intuition. discriminate H3.
          symmetry. apply (lt_sorted_count_occ_O _ _ _ H2 H).
        * apply H1.
  Qed.

End InsertionSort.
