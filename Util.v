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

