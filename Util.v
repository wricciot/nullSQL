Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Bool.Sumbool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega.

  Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

  Lemma eq_rect_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect x P p x eq_refl = p. 
  Proof.
    reflexivity.
  Qed.

  Lemma eq_rect_r_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect_r P p eq_refl = p. 
  Proof.
    reflexivity.
  Qed.

  Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
  Proof.
    rewrite H. reflexivity.
  Qed.

  Fixpoint cmap_length {A B : Type} (f : A -> B) l : List.length (List.map f l) = List.length l.
  refine (match l with List.nil => _ | List.cons h t => _ end).
  exact eq_refl.
  simpl. f_equal. apply cmap_length.
  Defined.

  (* sums a Vector of nats *)
  Definition vec_sum {k} (nl : Vector.t nat k) :=
    Vector.fold_right plus nl 0.

  Definition list_sum (nl : list nat) := List.fold_right plus 0 nl.

  Lemma flat_map_length {A B : Type} (f : A -> list B) (l : list A)
    : List.length (List.flat_map f l) = list_sum (List.map (fun x => List.length (f x)) l).
  elim l.
  + reflexivity.
  + intros a l0 IH. simpl. rewrite app_length.
    apply f_equal. exact IH.
  Defined.

  Lemma length_concat_list_sum (A : Type) (l : list (list A)) : 
    List.length (List.concat l) = list_sum (List.map (@List.length A) l).
  rewrite <- (map_id l) at 1. rewrite <- flat_map_concat_map.
  rewrite flat_map_length. apply f_equal. apply map_ext. auto.
  Defined.

  Definition cast (A B : Type) (e : A = B) (a : A) : B.
    rewrite <- e. exact a.
  Defined.

  (* naturally splits a Vector of size (m+n) into two Vectors of sizes m and n *)
  Fixpoint split {A} {m} {n} : Vector.t A (m+n) -> (Vector.t A m * Vector.t A n).
  refine
  (match m as m return Vector.t A (m+n) -> (Vector.t A m * Vector.t A n) with
   | 0 => fun v => (nil _,v)
   | S p => fun v => let h := Vector.hd v in let t := Vector.tl v in
      let (v1,v2) := split _ _ _ t in
      (Vector.cons _ h _ v1,v2)
   end).
  Defined.

  Lemma f_JMeq : forall A (T : A -> Type) (f : forall a, T a) x y, x = y -> f x ~= f y.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.

  Lemma existT_projT2_eq {A} {P : A -> Type} a (p1 p2 :  P a) (e : existT _ _ p1 = existT _ _ p2)
    : p1 = p2.
  Proof.
    transitivity (projT2 (existT P a p1)). reflexivity. 
    transitivity (projT2 (existT P a p2)). apply JMeq_eq. eapply (f_JMeq _ _ (@projT2 A P) _ _ e).
    reflexivity.
  Qed.

  Lemma existT_eq_elim {A} {P : A -> Type} {a} {b} {p1} {p2} (e : existT P a p1 = existT P b p2) :
    forall (Q:Prop), (a = b -> p1 ~= p2 -> Q) -> Q.
  Proof.
    intros. injection e. intros _ H1. generalize dependent p2. generalize dependent p1. 
    rewrite H1. intros. apply H; auto. apply eq_JMeq. apply (existT_projT2_eq _ _ _ e).
  Qed.


  Lemma cast_fun_app_JM A B A' B' B'' (ea : A = A') (eb : B = B') (eb' : B' = B'') :
    forall (e : (A -> B) = (A' -> B')) (f : A -> B) (x : A') (y : B''), 
    (forall x', x ~= x' -> f x' ~= y)
    -> cast _ _ e f x ~= y.
  Proof.
    rewrite ea, eb, eb'. intro e. rewrite (UIP_refl _ _ e). intros. simpl.
    apply H. reflexivity.
  Qed.

  Lemma JMeq_eq_rect A x (T : A -> Type) U t y e (u : U) : T y = U -> t ~= u -> eq_rect x T t y e ~= u.
  Proof.
    intros. generalize dependent t. rewrite e. simpl. intuition.
  Qed.

  Lemma JMeq_eq_rect_r A x (T : A -> Type) U t y e (u : U) : T y = U -> t ~= u -> @eq_rect_r _ x T t y e ~= u.
  Proof.
    intros. generalize dependent t. rewrite e. simpl. intuition.
  Qed.

  Lemma f_JMequal {A : Type} {B : A -> Type} {A' : Type} {B' : A' -> Type} 
    {ea : A = A'} {eb : B ~= B'} :
    forall (f : forall a, B a) (g : forall a', B' a') x y, f ~= g -> x ~= y -> f x ~= g y.
  Proof.
    generalize dependent eb. generalize dependent B'.
    rewrite <- ea. intros B' eb.
    eapply (eq_rect B (fun (B0 : A -> Type) =>
      forall (f : forall a : A, B a) (g : forall a' : A, B0 a') (x y : A), f ~= g -> x ~= y -> f x ~= g y) _ B' _).
    Unshelve.
    simpl. intros. rewrite H, H0. reflexivity.
    apply JMeq_eq. exact eb.
  Qed.

  Lemma f_JMequal_Prop {A : Type} {B : A -> Prop} {A' : Type} {B' : A' -> Prop} 
    {ea : A = A'} {eb : B ~= B'} :
    forall (f : forall a, B a) (g : forall a', B' a') x y, f ~= g -> x ~= y -> f x ~= g y.
  Proof.
    generalize dependent eb. generalize dependent B'.
    rewrite <- ea. intros B' eb.
    eapply (eq_rect B (fun (B0 : A -> Type) =>
      forall (f : forall a : A, B a) (g : forall a' : A, B0 a') (x y : A), f ~= g -> x ~= y -> f x ~= g y) _ B' _).
    Unshelve.
    simpl. intros. rewrite H, H0. reflexivity.
    apply JMeq_eq. exact eb.
  Qed.

  Lemma f_JMequal_pi {A : Prop} {B : A -> Type} {A' : Prop} {B' : A' -> Type} 
    {ea : A = A'} {eb : B ~= B'} :
    forall (f : forall a, B a) (g : forall a', B' a') x y, f ~= g -> f x ~= g y.
  (** not a corollary of the previous lemma, because here A = A' is (@eq Prop A A') rather than (@eq Type A A') *)
  Proof.
    generalize dependent eb. generalize dependent B'.
    rewrite <- ea. intros B' eb.
    eapply (eq_rect B (fun (B0 : A -> Type) =>
      forall (f : forall a : A, B a) (g : forall a' : A, B0 a') (x y : A), f ~= g -> f x ~= g y) _ B' _).
    Unshelve.
    simpl. intros. rewrite H. rewrite (proof_irrelevance _ x y). reflexivity.
    apply JMeq_eq. exact eb.
  Qed.

  Lemma cast_JMeq S T U e x (y : U) : x ~= y -> cast S T e x ~= y.
  Proof.
    generalize dependent x. rewrite e. simpl. intuition.
  Qed.

  Lemma cast_elim {P:Prop} {A} (B : Type) (a : A) : A = B -> (forall (b:B), a ~= b -> P) -> P.
  Proof.
    intros; subst. apply (H0 _ JMeq_refl).
  Qed.

  Lemma vector_append_nil_r {A} {n} (v : Vector.t A n): 
    append v (Vector.nil _) ~= v.
  Proof.
    induction v; intuition.
    simpl. eapply (f_JMequal (cons A h (n+0)) (cons A h n)). Unshelve.
    + eapply (f_JMeq _ _ (cons A h)). omega.
    + exact IHv.
    + f_equal. omega.
    + replace (n+0) with n. reflexivity. omega.
  Qed.

(*
  Lemma tech_commutative_join A B (l1 : list A) (l2 : list B) f g h :
    (forall x, count_occ Nat.eq_dec (List.map f l1) x = count_occ Nat.eq_dec (List.map g (List.map h l1)) x) ->
    (forall x, count_occ Nat.eq_dec (List.map g (List.map h l1)) x = count_occ Nat.eq_dec (List.map g l2) x) ->
    forall x, count_occ Nat.eq_dec (List.map f l1) x = count_occ Nat.eq_dec (List.map g l2) x.
  Proof.
    intuition. etransitivity. apply H. apply H0.
  Qed.

  Axiom tech2_commutative_join : forall A B C (l : list A) (f : A -> C) (g : B -> C) (h : A -> B),
    (forall x, f x = g (h x)) ->
    List.map f l = List.map g (List.map h l).

  Axiom tech3_commutative_join : forall A B Hdec g (h : A -> B) l1 l2,
    (forall x, count_occ Hdec (List.map h l1) x = count_occ Hdec l2 x) ->
    forall x, count_occ Nat.eq_dec (List.map g (List.map h l1)) x = count_occ Nat.eq_dec (List.map g l2) x.

  Axiom tech4_commutative_join : forall A B HdecA HdecB (h : A -> B) p1 p2 l1 l2,
    (forall x, count_occ HdecA l1 x = count_occ HdecB l2 (h x) /\ p1 x = p2 (h x)) ->
    forall x, count_occ HdecB (List.map h (List.filter p1 l1)) x = count_occ HdecB (List.filter p2 l2) x.
*) 

  Definition flip {A} {m} {n} : Vector.t A (m + n) -> Vector.t A (n + m) :=
    fun v => let (v1,v2) := split v in Vector.append v2 v1.

  Lemma cast_fun_app A B A' B' (ea : A = A') (eb : B = B') :
    forall (e : (A -> B) = (A' -> B')) (f : A -> B) (x : A') (y : B'), 
    (forall x', x ~= x' -> f x' ~= y)
    -> cast _ _ e f x = y.
  Proof.
    rewrite ea, eb. intro e. rewrite (UIP_refl _ _ e). intros. simpl.
    apply JMeq_eq. apply H. reflexivity.
  Qed.

  Lemma split_0_l {A} {n} (v : Vector.t A (0 + n)) :
    forall (v0 : Vector.t A n), v ~= v0 <-> split v = (Vector.nil _, v0).
  Proof.
    simpl. intuition.
    + rewrite H; reflexivity.
    + injection H; intuition; rewrite H0; reflexivity.
  Qed.

  Lemma hd_equal {A} {m} {n} (v1 : Vector.t A (S m)) (v2 : Vector.t A (S n)) :
    m = n -> v1 ~= v2 -> hd v1 = hd v2.
  Proof.
    intro. subst. intro. rewrite H. reflexivity.
  Qed.

  Lemma tl_equal {A} {m} {n} (v1 : Vector.t A (S m)) (v2 : Vector.t A (S n)) :
    m = n -> v1 ~= v2 -> tl v1 ~= tl v2.
  Proof.
    intro. subst. intro. rewrite H. reflexivity.
  Qed.

  Lemma cons_equal {A} : forall h1 h2 n1 n2 t1 t2,
    h1 = h2 -> n1 = n2 -> t1 ~= t2 -> cons A h1 n1 t1 ~= cons A h2 n2 t2.
  Proof.
    intros. generalize t1 t2 H1; clear t1 t2 H1. rewrite H, H0.
    intros. rewrite H1. reflexivity.
  Qed.

  Lemma fst_split_0_r {A} {n} (v : Vector.t A (n + 0)) : fst (split v) ~= v.
  Proof.
    generalize dependent v. induction n; simpl.
    + intro. eapply (case0 _ _ v). Unshelve. reflexivity.
    + intros. eapply (caseS' v). simpl. intros.
      replace (split t) with (fst (split t), snd (split t)). simpl.
      apply cons_equal. reflexivity. omega. apply IHn.
      rewrite surjective_pairing. reflexivity.
  Qed.

  Lemma split_ind {A} {m} {n} (v : Vector.t A (m + n)) :
    forall (P : forall m n, (Vector.t A m * Vector.t A n) -> Prop),
    (forall v1 v2, v = append v1 v2 -> P m n (v1,v2)) ->
    P m n (split v).
  Proof.
    induction m; simpl; intuition.
    rewrite (surjective_pairing (split (tl v))). apply H. apply JMeq_eq.
    eapply (IHm (tl v) (fun m0 n0 v0 => v ~= append (cons A (hd v) _ (fst v0)) (snd v0))).
    intros. simpl. rewrite (Vector.eta v). simpl. apply eq_JMeq. f_equal. exact H0.
  Qed.

  Lemma split_0_r {A} {n} (v : Vector.t A (n + 0)) :
    forall (v0 : Vector.t A n), v ~= v0 <-> split v = (v0, Vector.nil _).
  Proof.
    induction n; simpl; intuition.
    + f_equal. eapply (case0 _ _ v0). eapply (case0 (fun v => v = nil A) _ v). Unshelve.
      reflexivity. reflexivity.
    + injection H. intuition. subst. reflexivity.
    + generalize dependent H. apply (caseS' v). apply (caseS' v0).
      intuition. simpl. destruct (IHn t0 t). rewrite H0.
      f_equal. f_equal. 
      enough (hd (cons A h0 (n+0) t0) = hd (cons A h n t)). exact H2. apply hd_equal.
      omega. exact H.
      enough (tl (cons A h0 (n+0) t0) ~= tl (cons A h n t)). exact H2. apply tl_equal.
      omega. exact H.
    + generalize dependent H. apply (caseS' v). apply (caseS' v0).
      intuition. simpl in H. replace (split t0) with (fst (split t0), snd (split t0)) in H.
      enough (fst (cons A h0 n (fst (split t0)), snd (split t0)) ~= fst (cons A h n t, nil A)).
      simpl in H0. rewrite <- H0. apply cons_equal. reflexivity. apply plus_0_r. symmetry. apply fst_split_0_r.
      rewrite H. reflexivity. rewrite surjective_pairing. reflexivity.
  Qed.

  Lemma vec_append_inj {A} {m} {n} {v1 v2 : Vector.t A m} {v3 v4 : Vector.t A n}
    : append v1 v3 = append v2 v4 -> v1 = v2 /\ v3 = v4.
  Proof.
    induction m; simpl.
    + eapply (case0 (fun v0 => append v0 v3 = append v2 v4 -> v0 = v2 /\ v3 = v4)).
      eapply (case0 (fun v0 => append (nil A) v3 = append v0 v4 -> nil A = v0 /\ v3 = v4)).
      simpl; intuition.
    + eapply (caseS' v1). eapply (caseS' v2).
      intros h2 t2 h1 t1. simpl. intro H.
      destruct (cons_inj H). destruct (IHm _ _ H1). subst. intuition.
  Qed.

  Lemma flip_inv {A} {m} {n} (v1 : Vector.t A (m + n)) (v2 : Vector.t A (n + m)) : 
    flip v1 = v2 -> v1 = flip v2.
  Proof.
    intro. rewrite <- H. clear H v2. unfold flip. apply JMeq_eq.
    eapply (split_ind v1). intros.
    eapply (split_ind (append v2 v0)). intros.
    rewrite H. destruct (vec_append_inj H0). subst. reflexivity.
  Qed.

  Lemma to_list_append {A} {m} {n} (v1:Vector.t A m) (v2:Vector.t A n) : 
    to_list (append v1 v2) = to_list v1 ++ to_list v2.
  Proof.
    elim v1; simpl; intuition.
    unfold to_list. f_equal. exact H.
  Qed.

  Lemma JMeq_cast_eq S T e x y : x ~= y -> cast S T e x = y.
  Proof.
    generalize x. rewrite e. simpl. intuition. apply JMeq_eq. exact H.
  Qed.

  Lemma eq_vector_to_list {A} {m} {n} (v1 : Vector.t A m) (v2 : Vector.t A n) :
    m = n -> to_list v1 = to_list v2 -> v1 ~= v2.
  Proof.
    intro. generalize dependent v1. rewrite H. intro.
    apply (rect2 (fun {n} w1 w2 => to_list w1 = to_list w2 -> w1 ~= w2)); intuition.
    unfold to_list in H1; simpl in H1. injection H1.
    clear H1; intros. rewrite H2.
    eapply (f_JMeq _ _ (cons A b n0)). apply JMeq_eq. apply H0. exact H1.
  Qed.

  Lemma tl_append : forall A m n (v1 : Vector.t A (S m)) (v2 : Vector.t A n), tl (append v1 v2) = append (tl v1) v2.
  Proof.
    intros. rewrite (Vector.eta v1). simpl. reflexivity.
  Qed.

  Theorem list_ind2 (A B : Type) (P : list A -> list B -> Type) :
      P List.nil List.nil ->
      (forall a al b bl, length al = length bl -> P al bl -> P (a::al) (b::bl)) ->
      forall al bl, length al = length bl -> P al bl.
  Proof.
    intros Hnil Hcons al. induction al.
    + intro. destruct bl; intuition. discriminate H.
    + intro. destruct bl; intuition. discriminate H.
  Qed.

  Lemma map_fst_combine A B (al : list A) (bl : list B) : 
    length al = length bl -> List.map fst (combine al bl) = al.
  Proof.
    intros. eapply (list_ind2 _ _ (fun al bl => List.map fst (combine al bl) = al) _ _ _ _ H). Unshelve.
    + reflexivity.
    + simpl; intros. rewrite H1. reflexivity.
  Qed.

  Lemma length_combine A B (al : list A) (bl : list B) : 
    length al = length bl -> length (combine al bl) = length al.
  Proof.
    intros. rewrite <- (map_fst_combine _ _ _ _ H) at 2. rewrite List.map_length. reflexivity.
  Qed.

  Fixpoint rmone A (eq_dec : forall x y : A, {x = y}+{x <> y}) a (l : list A) : list A :=
      match l with
        | List.nil => List.nil
        | x::xs => if eq_dec x a then xs else x::(rmone A eq_dec a xs)
      end.

  Lemma count_occ_rmone_zero A Hdec a l : 
    count_occ Hdec l a = 0 -> count_occ Hdec (rmone A Hdec a l) a = 0.
  Proof.
    elim l. intuition.
    simpl. intros h t IH. destruct (Hdec h a).
    + intro H. discriminate H.
    + simpl. intro H. destruct (Hdec h a). intuition.
      exact (IH H).
  Qed.

  Lemma count_occ_rmone A Hdec a l :
    forall n, count_occ Hdec l a = S n -> count_occ Hdec (rmone A Hdec a l) a = count_occ Hdec l a - 1.
  Proof.
    elim l; simpl.
    + intuition.
    + intros h t IH n. destruct (Hdec h a).
      - intro Hta. simpl. intuition.
      - simpl. destruct (Hdec h a). intuition.
        apply IH.
  Qed.

  Lemma count_occ_rmone_r A Hdec a l :
    forall n, count_occ Hdec l a = S n -> count_occ Hdec l a = S (count_occ Hdec (rmone A Hdec a l) a).
  Proof.
    intros. rewrite H. f_equal. rewrite (count_occ_rmone _ _ _ _ _ H). rewrite H. omega.
  Qed.

  Lemma count_occ_list_sum Hdec n l :
    O < count_occ Hdec l n -> list_sum l = n + list_sum (rmone nat Hdec n l).
  Proof.
    elim l; simpl.
    + intro. contradiction (Lt.lt_0_neq _ H). reflexivity.
    + intros m l0 IH. destruct (Hdec m n).
      - rewrite e. intros _. reflexivity.
      - simpl. intro H. rewrite (IH H). omega.
  Qed.

  Lemma list_sum_ext Hdec l1 :
    forall l2, (forall x, count_occ Hdec l1 x = count_occ Hdec l2 x) ->
    list_sum l1 = list_sum l2.
  Proof.
    elim l1; simpl.
    + intros. replace l2 with (@List.nil nat). reflexivity.
      destruct l2; auto. pose (e := H n); clearbody e; simpl in e. destruct (Hdec n n).
      - discriminate e.
      - contradiction n0. reflexivity.
    + intros x l1' IH l2 Hcount. assert (0 < count_occ Hdec l2 x).
      rewrite <- Hcount. destruct (Hdec x x). omega. contradiction n. reflexivity.
      rewrite (count_occ_list_sum _ _ _ H). f_equal. apply IH.
      intro y. pose (Hcount' := Hcount y); clearbody Hcount'.
      destruct (Hdec x y).
      - subst. assert (exists n, count_occ Hdec l2 y = S n).
        inversion H; eexists; intuition. destruct H0.
        erewrite count_occ_rmone.
        * rewrite <- Hcount'. omega.
        * exact H0.
      - rewrite Hcount'. elim l2; auto.
        intros z l2' IHin. simpl. destruct (Hdec z x).
        * destruct (Hdec z y); auto.
          contradiction n. rewrite <- e, e0. reflexivity.
        * simpl. destruct (Hdec z y); simpl.
          ++ f_equal. apply IHin.
          ++ apply IHin.
  Qed.

  Lemma skipn_app_l : forall A (l1 l2: list A) n, n <= length l1 -> skipn n (l1++l2) = skipn n l1 ++ l2.
  Proof.
    intros. generalize dependent n. induction l1.
    + intros. simpl in H; inversion H; auto.
    + intros. destruct n; auto. simpl. apply IHl1. simpl in H. omega.
  Qed.

  Lemma filter_true A p (l : list A) : 
    (forall x, List.In x l -> p x = true) -> filter p l = l.
  Proof.
    elim l. auto.
    intros h t IH Hp. simpl. rewrite Hp.
    + f_equal. apply IH. intros. apply Hp. right. exact H.
    + left. reflexivity.
  Qed.

  Lemma count_occ_In_Sn {A} Hdec (x : A) l: List.In x l -> exists n, count_occ Hdec l x = S n.
  Proof.
    intro Hx. assert (count_occ Hdec l x > 0).
    apply count_occ_In. exact Hx.
    inversion H; eexists; auto.
  Qed.

  Lemma in_rmone A Hdec a x l2 : List.In x (rmone A Hdec a l2) -> List.In x l2.
  Proof.
    elim l2; simpl; intuition. destruct (Hdec a0 a); intuition.
    inversion H0; intuition.
  Qed.

  Lemma in_rmone_neq A Hdec a x l2 : a <> x -> List.In x l2 -> List.In x (rmone A Hdec a l2).
  Proof.
    intro Hax. elim l2; intuition.
    inversion H0; intuition.
    + simpl. destruct (Hdec a0 a); intuition.
      - subst. contradiction Hax. reflexivity.
      - rewrite H1. left. reflexivity.
    + simpl. destruct (Hdec a0 a); intuition.
  Qed.

  Lemma nodup_rmone A Hdec a l2 : NoDup l2 -> NoDup (rmone A Hdec a l2).
  Proof.
    elim l2; intuition. inversion H0.
    simpl. destruct (Hdec a0 a).
    + exact H4.
    + constructor. intro. apply H3. apply (in_rmone _ _ _ _ _ H5).
      apply H. inversion H0; intuition.
  Qed.

  Lemma incl_rmone {A} Hdec (l1 l2 : list A) x : 
    NoDup l1 -> incl l1 (x :: l2) -> incl (rmone A Hdec x l1) l2.
  Proof.
    intros H H1. intro. intro H2. pose (H2' := in_rmone _ _ _ _ _ H2). clearbody H2'.
    pose (H1' := H1 _ H2'). clearbody H1'. assert (a <> x).
    + intro. subst. generalize H H2. elim l1.
      - simpl; intuition.
      - intros a l IH Hnodup. simpl. destruct (Hdec a x).
        * subst. intro. inversion Hnodup. contradiction H5.
        * intro. destruct H0. contradiction n. apply IH. inversion Hnodup; auto. exact H0.
    + destruct H1'; auto. subst. contradiction H0. reflexivity.
  Qed.

  Lemma map_filter_tech {A} {B} {Hdec} {Hdec'} (f : A -> B) p x y l : 
    p x = true -> y = f x -> List.In x l ->
    count_occ Hdec (List.map f (filter p (rmone _ Hdec' x l))) y 
    = count_occ Hdec (rmone _ Hdec y (List.map f (filter p l))) y.
  Proof.
    intros H H0. elim l; auto.
    intros a l' IH Hl. simpl. destruct (Hdec' a x).
    + rewrite e. rewrite H. simpl. destruct (Hdec (f x) y).
      - reflexivity.
      - contradiction n. symmetry. exact H0.
    + simpl. assert (List.In x l'). inversion Hl. contradiction n. exact H1. 
      destruct (p a) eqn:Hp; simpl.
      - destruct (Hdec (f a) y).
        * rewrite IH; auto. symmetry. 
          assert (List.In y (List.map f (filter p l'))).
          rewrite H0. apply in_map. apply filter_In; split; auto.
          destruct (count_occ_In_Sn Hdec _ _ H2).
          eapply count_occ_rmone_r. exact H3.
        * rewrite IH; auto. simpl. destruct (Hdec (f a) y). contradiction n0. reflexivity.
      - apply IH. inversion Hl; auto.
  Qed.

  Lemma count_occ_map_filter_rmone_tech {A} {B} {Hdec} {Hdec'} (f : A -> B) p x y l:
    f x <> y ->
    count_occ Hdec (List.map f (filter p (rmone _ Hdec' x l))) y
    = count_occ Hdec (List.map f (filter p l)) y.
  Proof.
    intros. elim l; auto.
    intros a l' IH. simpl. destruct (Hdec' a x).
    + rewrite e. destruct (p x); simpl.
      - destruct (Hdec (f x) y); simpl.
        * contradiction H.
        * reflexivity.
      - reflexivity.
    + simpl. destruct (p a); simpl.
      - destruct (Hdec (f a) y); simpl.
        * f_equal. apply IH.
        * apply IH.
      - apply IH.
  Qed.

  Lemma filter_rmone_false {A} {Hdec} p (x : A) l : p x = false -> filter p (rmone _ Hdec x l) = filter p l.
  Proof.
    intro. elim l; auto.
    intros a l' IH. simpl. destruct (Hdec a x); simpl.
    + rewrite e. rewrite H. reflexivity.
    + destruct (p a).
      - rewrite IH. reflexivity.
      - exact IH.
  Qed.

  Lemma NoDup_filter {A} (f : A -> bool) l : List.NoDup l -> List.NoDup (filter f l).
  Proof.
    elim l; simpl; auto.
    intros. inversion H0. destruct (f a); simpl; auto.
    constructor; auto. intro; apply H3.
    destruct (proj1 (filter_In f a l0) H5). exact H6.
  Qed.

  Lemma exists_vector_append A m n p (v : Vector.t A m) : 
    m = n + p -> exists (w1 : Vector.t A n) (w2 : Vector.t A p), v ~= append w1 w2.
  Proof.
    intro H. generalize dependent v. rewrite H. intro v.
    exists (fst (split v)). exists (snd (split v)).
    apply (split_ind v). intuition. rewrite H0. reflexivity.
  Qed.

  Lemma list_length_decompose A (l : list A) m n: length l = S (m + n) -> 
    exists a l1 l2, length l1 = m /\ length l2 = n /\ l = l1 ++ a :: l2.
  Proof.
    generalize dependent l. induction m; intuition.
    + destruct l; simpl in H; try discriminate. injection H.
      exists a. exists List.nil. exists l. intuition.
    + destruct l; simpl in H; try discriminate. injection H. intro.
      decompose record (IHm _ H0).
      exists x. exists (a::x0). exists x1. simpl. intuition. rewrite H4. reflexivity.
  Qed.

  Lemma length_skipn {A} (l : list A) :
    forall n, length (skipn n l) = length l - n.
  Proof.
    induction l; simpl; intuition; case n; intuition.
  Qed.

  Lemma funext_JMeq {A} {B} {A'} {B'} :
    A = A' -> B = B' -> forall (f : A -> B) (g : A' -> B'),
    (forall x y, x ~= y -> f x ~= g y) -> f ~= g.
  Proof.
    intros e1 e2. rewrite e1, e2.
    intros. apply eq_JMeq. extensionality x. apply JMeq_eq. apply H. reflexivity.
  Qed.

  Definition unopt {A} : forall (x : option A), x <> None -> A.
    refine (fun x => match x as x0 return (x0 <> None -> A) with Some x' => fun _ => x' | None => _ end).
    intro Hfalse. contradiction Hfalse. reflexivity.
  Defined.

  Definition nth_lt {A} : forall (l : list A) n, n < length l -> A.
    refine (fun l n Hn => unopt (nth_error l n) _). apply nth_error_Some. exact Hn.
  Defined.

  Lemma le_list_sum_count_occ H l1 : 
    forall l2, (forall x, count_occ H l1 x <= count_occ H l2 x) ->
    list_sum l1 <= list_sum l2.
  elim l1. intuition.
  intros h t IH l2 Hcount. rewrite (count_occ_list_sum H h l2).
  + simpl. apply plus_le_compat_l. apply IH. intro.
    replace (count_occ H t x) with (count_occ H (rmone nat H h (h::t)) x).
    - pose (Hx := (Hcount x)). simpl in Hx. clearbody Hx. destruct (H h x).
      rewrite e. cut (exists m, count_occ H l2 x = S m).
      * intro Hcut. decompose record Hcut.
        erewrite (count_occ_rmone _ _ _ l2).
        erewrite (count_occ_rmone _ _ _ (x :: t)).
        ++ apply minus_le_compat_r. rewrite e in Hcount. apply Hcount.
        ++ simpl. destruct (H x x); intuition.
        ++ exact H0.
      * inversion Hx.
        ++ exists (count_occ H t x). reflexivity.
        ++ exists m. reflexivity.
      * simpl. destruct (H h h); intuition. replace (count_occ H (rmone nat H h l2) x) with (count_occ H l2 x).
        ++ exact Hx.
        ++ elim l2; intuition.
           simpl. destruct (H a x) eqn:e'.
           -- destruct (H a h).
              ** rewrite e0 in e1. rewrite e1 in n. contradiction n.
              ** simpl. destruct (H a x); intuition.
           -- destruct (H a h); intuition. simpl. rewrite e'. apply H0.
    - simpl. destruct (H h h); intuition.
  + eapply (lt_le_trans _ _ _ _ (Hcount h)). Unshelve.
    simpl. destruct (H h h); intuition.
  Qed.

  Lemma le_count_occ_cons A Hdec (a : A) l x : count_occ Hdec l x <= count_occ Hdec (a::l) x.
  Proof.
    simpl. destruct (Hdec a x); intuition.
  Qed.

  Lemma count_occ_not_in A Hdec (a x : A) l : a <> x -> count_occ Hdec l x = count_occ Hdec (rmone A Hdec a l) x.
  Proof.
    intro. elim l; auto.
    intros h t IH. simpl. destruct (Hdec h x); intuition.
    + destruct (Hdec h a); intuition.
      - contradiction H. rewrite <- e0. exact e.
      - simpl. destruct (Hdec h x); intuition.
    + destruct (Hdec h a); intuition.
      simpl. destruct (Hdec h x); intuition.
  Qed.

  Lemma list_sum_map_rmone A Hdec g l (a : A) : 
    forall x, count_occ Hdec l a = S x -> list_sum (List.map g l) = g a + list_sum (List.map g (rmone A Hdec a l)).
  Proof.
    elim l; simpl; intuition.
    destruct (Hdec a0 a); intuition.
    + rewrite e. reflexivity.
    + simpl. rewrite (H _ H0). omega.
  Qed.

  Lemma fun_ext_dep A B C (e : A = B) : 
    forall (f : A -> C) (g : B -> C), (forall (x : A) (y : B), x ~= y -> f x = g y) -> f ~= g.
  Proof.
    rewrite e. intros.
    apply eq_JMeq. extensionality z.
    apply H. reflexivity.
  Qed.

  Lemma eq_cast_fun A B C (e : B = A) :
    forall (ef : (A -> C) = (B -> C)) (f : A -> C) (x : B), cast _ _ ef f x = f (cast _ _ e x).
  Proof.
    rewrite e. intro. rewrite (UIP_refl _ _ ef). intros.
    unfold cast. reflexivity.
  Qed.

  Lemma le_list_sum_memb_tech A (Hdec : forall x y : A, { x = y } + { x <> y }) f g (l1 : list A) (Hfg : forall x, f x <= g x) : 
    forall l2, NoDup l1 -> NoDup l2 -> (forall x, List.In x l1 -> 0 < f x -> List.In x l2) ->
    list_sum (List.map f l1) <= list_sum (List.map g l2).
  elim l1; intuition.
  simpl. destruct (f a) eqn:Hfa.
  + apply H; auto; intros.
    - inversion H0; auto.
    - apply H2; auto. right. exact H3.
  + replace (list_sum (List.map g l2)) with (g a + list_sum (List.map g (rmone A Hdec a l2))).
    - rewrite <- Hfa. apply plus_le_compat; auto. apply H.
      * inversion H0; auto.
      * apply nodup_rmone. exact H1.
      * intros y Hy Hfy. cut (a <> y).
        ++ intro Hay. apply in_rmone_neq. 
           -- exact Hay.
           -- apply H2; intuition.
        ++ inversion H0; auto. intro. contradiction H5. rewrite H7. exact Hy.
    - cut (List.In a l2).
      * intro Hcut. rewrite (count_occ_list_sum Nat.eq_dec (g a) (List.map g l2)).
        ++ f_equal. generalize Hcut; clear Hcut. elim l2; intuition.
           destruct Hcut; simpl.
           -- rewrite H4. destruct (Nat.eq_dec (g a) (g a)); intuition. destruct (Hdec a a); intuition.
           -- destruct (Hdec a0 a); intuition.
              ** rewrite e. destruct (Nat.eq_dec (g a) (g a)); intuition.
              ** destruct (Nat.eq_dec (g a0) (g a)); intuition.
                 +++ simpl. rewrite e. symmetry. cut (exists n, count_occ Hdec l0 a = S n).
                     intro Hcut; decompose record Hcut. apply (list_sum_map_rmone _ _ _ _ _ _ H3).
                     destruct (count_occ_In Hdec l0 a).
                     pose (H3 H4). inversion g0; eexists; reflexivity.
                 +++ simpl. f_equal. apply H5.
        ++ generalize Hcut; clear Hcut. elim l2; simpl.
           -- intro. contradiction Hcut.
           -- intros. destruct Hcut.
              ** rewrite H4. destruct (Nat.eq_dec (g a) (g a)); intuition.
              ** pose (H3 H4). destruct (Nat.eq_dec (g a0) (g a)); omega.
      * apply H2. left. reflexivity. omega.
  Qed.

  Lemma le_list_sum_memb A Hdec f g (l1 l2 : list A) (Hfg : forall x, f x <= g x) : 
    (forall x, count_occ Hdec l1 x <= count_occ Hdec l2 x) ->
    list_sum (List.map f l1) <= list_sum (List.map g l2).
  intro Hcount. generalize l2 Hcount. clear l2 Hcount. elim l1; intuition.
  simpl. cut (exists n, count_occ Hdec l2 a = S n).
  + intro Hcut. decompose record Hcut. clear Hcut.
    replace (list_sum (List.map g l2)) with (g a + list_sum (List.map g (rmone A Hdec a l2))).
    - apply plus_le_compat; auto. apply H. 
      intro y. destruct (Hdec a y).
      * rewrite e in H0. rewrite e. rewrite (count_occ_rmone _ _ _ _ _ H0). 
        rewrite H0. transitivity x. pose (Hy := Hcount y). clearbody Hy.
        rewrite H0 in Hy. simpl in Hy. destruct (Hdec a y); intuition.
        omega.
      * replace (count_occ Hdec (rmone A Hdec a l2) y) with (count_occ Hdec l2 y).
        ++ transitivity (count_occ Hdec (a :: l) y).
           -- apply le_count_occ_cons.
           -- apply Hcount.
        ++ apply count_occ_not_in. auto.
    - rewrite (list_sum_map_rmone _ _ _ _ _ _ H0). reflexivity.
  + pose (Ha := Hcount a); clearbody Ha; simpl in Ha. destruct (Hdec a a); intuition.
    inversion Ha; eexists; reflexivity.
  Qed.

  Lemma le_list_sum_memb_f A Hdec f (l1 l2 : list A) : 
    (forall x, count_occ Hdec l1 x <= count_occ Hdec l2 x) ->
    list_sum (List.map f l1) <= list_sum (List.map f l2).
  Proof.
    apply le_list_sum_memb. auto.
  Qed.

  Lemma le_list_sum_map_f_g A f g (l : list A) : 
    (forall x, f x <= g x) ->
    list_sum (List.map f l) <= list_sum (List.map g l).
  Proof.
    intro Hfg. elim l; intuition.
    simpl. apply plus_le_compat;auto.
  Qed.

  Lemma le_1_or : forall x, x <= 1 -> x = 0 \/ x = 1.
  Proof.
    intros. inversion H. auto. inversion H1. auto.
  Qed.

  Lemma list_rect2 {A} {B} {P : list A -> list B -> Type} :
         P Datatypes.nil Datatypes.nil -> 
         (forall a1 a2 l1 l2, length l1 = length l2 -> P l1 l2 -> P (a1 :: l1) (a2 :: l2)) -> 
         forall l1 l2, length l1 = length l2 -> P l1 l2.
  Proof.
    intros Hbase Hind l1. elim l1.
    + intro; destruct l2; intuition. simpl in H. discriminate H.
    + intros a l1' IH l2. destruct l2; intuition. simpl in H. discriminate H.
  Qed.

  Lemma Vector_cons_equal {A} {m} {n} a1 a2 (v1 : Vector.t A m) (v2 : Vector.t A n) :
    m ~= n -> a1 ~= a2 -> v1 ~= v2 -> cons A a1 m v1 ~= cons A a2 n v2.
  Proof.
    intro. generalize v1; clear v1. rewrite H. intros. rewrite H0, H1. reflexivity.
  Qed.

  Lemma of_list_equal {A} (l1 l2 : list A) :
    l1 = l2 -> of_list l1 ~= of_list l2.
  Proof.
    intro. rewrite H. reflexivity.
  Qed.

  Definition projT1_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : projT1 u = projT1 v
    := f_equal (@projT1 _ _) p.

  Definition projT2_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : @eq_rect _ _ _ (projT2 u) _ (projT1_eq p) = projT2 v.
  Proof.
    rewrite p. reflexivity.
  Qed.

  Lemma list_In_vec_In {A} (a : A) (l : list A) : List.In a l -> Vector.In a (Vector.of_list l).
  Proof.
    elim l.
    + intro H. contradiction H.
    + intros a0 l0 IH H. destruct H.
      - rewrite H. constructor.
      - constructor. apply IH. exact H.
  Qed.

  Lemma bool_eq_P (P : Prop) b1 b2 : (b1 = true <-> P) -> (b2 = true <-> P) -> b1 = b2.
  Proof.
    Bool.destr_bool.
    + apply H. apply H0. reflexivity.
    + symmetry. apply H0. apply H. reflexivity.
  Qed.

  Lemma to_list_eq {A} {m} (ul : Vector.t A m) {n} (vl : Vector.t A n) : m = n -> ul ~= vl -> to_list ul = to_list vl.
  Proof.
    intro e. generalize ul; clear ul; rewrite e; intros ul e'. rewrite e'. reflexivity.
  Qed.

  Lemma hd_eq {A} {m} (ul : Vector.t A (S m)) {n} (vl : Vector.t A (S n)) : m = n -> ul ~= vl -> hd ul = hd vl.
  Proof.
    intro e. generalize ul; clear ul; rewrite e; intros ul e'. rewrite e'. reflexivity.
  Qed.

  Lemma tl_eq {A} {m} (ul : Vector.t A (S m)) {n} (vl : Vector.t A (S n)) : m = n -> ul ~= vl -> tl ul ~= tl vl.
  Proof.
    intro e. generalize ul; clear ul; rewrite e; intros ul e'. rewrite e'. reflexivity.
  Qed.

  Lemma split_n_0 {A} {n} : forall (ul1 : Vector.t A (n+0)) (ul2 : Vector.t A n), ul1 ~= ul2 -> split ul1 ~= (ul2, nil A).
  Proof.
    elim n.
    + simpl. intros. 
      eapply (Vector.case0 (fun ul0 => (nil A, ul0) ~= (ul2, nil A))).
      eapply (Vector.case0 (fun ul0 => (nil A, nil A) ~= (ul0, nil A))). reflexivity.
    + clear n. intros n IH ul1 ul2. simpl. intro.
      generalize (@JMeq_refl _ ul1).
      eapply (Vector.caseS (fun n0 ul0 => ul1 ~= ul0 -> (let (v1,v2) := split (tl ul1) in (cons A (hd ul1) n v1, v2)) ~= (ul2, nil A))).
      intros h n0. replace n0 with (n0 + 0).
      - intro tl1. intro H1. cut (tl ul1 ~= tl ul2).
        * intro Hcut. pose (IH' := IH _ _ Hcut); clearbody IH'.
          pose (f := fun n (x : Vector.t A n * Vector.t A 0) => let (v1, v2) := x in (cons A (hd ul1) n v1, v2)).
          cut (f _ (split (tl ul1)) ~= f _ (tl ul2, nil A)).
          ++ unfold f. intro Hf. eapply (JMeq_trans Hf). apply eq_JMeq. f_equal.
            replace ul2 with (cons A (hd ul2) n (tl ul2)).
            -- f_equal. apply hd_eq. apply plus_0_r. exact H.
            -- eapply (Vector.caseS (fun n0 ul0 => cons A (hd ul0) n0 (tl ul0) = ul0)). intuition.
          ++ rewrite IH'. reflexivity.
        * apply tl_eq. apply plus_0_r. exact H.
      - apply plus_0_r.
  Qed.

  Lemma nth_error_Some_nth {A} {n} (ul : Vector.t A n) : forall k (Hk : k < n),
    nth_error (to_list ul) k = Some (nth ul (Fin.of_nat_lt Hk)).
  Proof.
    elim ul.
    + intros k Hk. absurd (k < 0). omega. exact Hk.
    + clear n ul. intros h n ul IH k. destruct k.
      - simpl. intuition.
      - intro Hk. transitivity (nth_error (to_list ul) k).
        * reflexivity.
        * cut (k < n).
          ++ intro Hk'. rewrite (IH _ Hk'). f_equal.
            replace (Fin.of_nat_lt Hk) with (Fin.FS (Fin.of_nat_lt Hk')).
            -- reflexivity.
            -- transitivity (Fin.of_nat_lt (le_n_S _ _ Hk')).
              ** simpl. f_equal. apply Fin.of_nat_ext.
              ** apply Fin.of_nat_ext.
          ++ omega.
  Qed.

  Lemma if_true A b x y (P : A -> Prop) : b = true -> P x -> P (if b then x else y).
  Proof.
    intros. rewrite H. exact H0.
  Qed.

  Lemma if_false A b x y (P : A -> Prop) : b = false -> P y -> P (if b then x else y).
  Proof.
    intros. rewrite H. exact H0.
  Qed.

  Lemma if_elim A (b : bool) x y (P : A -> Prop) : P x -> P y -> P (if b then x else y).
  Proof.
    intros. destruct b; auto.
  Qed.

  Lemma eq_rect_dep : forall (A : Type) (x : A) (P : forall (a : A), x = a -> Type), P x eq_refl ->
    forall y : A, forall e : x = y, P y e.
  Proof.
    intros. rewrite <- e. apply X.
  Qed.

  Lemma bool_contrapos b1 b2 : (b1 = true -> b2 = true) -> b2 = false -> b1 = false.
  Proof.
    Bool.destr_bool. discriminate (H eq_refl).
  Qed.

  Lemma coimpl_trans {P Q R : Prop} (H1 : P <-> Q) (H2 : Q <-> R) : P <-> R.
  Proof.
    intuition.
  Qed.

  Lemma coimpl_sym {P Q : Prop} (H : P <-> Q) : Q <-> P.
  Proof.
    intuition.
  Qed.

  Lemma bool_orb_elim (b1 b2 : bool) (P : Prop) : 
    (b1 = true -> P) -> (b2 = true -> P) -> (b1 || b2)%bool = true -> P.
  Proof.
    Bool.destr_bool; auto.
  Qed.

  Lemma vector_append_cons {A m n} (v : Vector.t A m) (w : Vector.t A (S n)) : 
    append v w ~= append (append v (cons A (hd w) _ (nil _))) (tl w).
  Proof.
    induction v; simpl.
    + rewrite <- (Vector.eta w). reflexivity.
    + eapply (f_JMequal (cons _ _ _) (cons _ _ _)). Unshelve.
      - eapply (f_JMequal (cons _ _) (cons _ _)). Unshelve. reflexivity. apply eq_JMeq. omega. reflexivity. reflexivity.
      - exact IHv.
      - f_equal. omega.
      - replace (n0 + 1 + n) with (n0 + S n). reflexivity. omega.
  Qed.

  Lemma unopt_elim {A} (x : option A) H (P : A -> Prop) : 
    (forall y, x = Some y -> P y) ->
    P (unopt x H).
  Proof.
    destruct x; intuition. contradiction H. reflexivity.
  Qed.

