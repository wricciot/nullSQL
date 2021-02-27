(* if we do not remove the dependency on Syntax, we can't compile this until we fix syntax *)

Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Bool.Sumbool JMeq Common Syntax
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Syntax AbstractRelation Util.

Module Facts (Db : DB) (Sql : SQL Db).

  Import Db.
  Import Sql.

(*** XXX: currently in Translation2V, needs to be shared (e.g. in Facts.v) ***)
  Lemma eq_memb_dep m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n) r1 r2,
    S1 ~= S2 -> r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2.
  Proof.
    rewrite e. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma eq_times_dep m1 m2 n1 n2 (e1 : m1 = n1) (e2 : m2 = n2) :
    forall (R1 : Rel.R m1) (R2 : Rel.R m2) (S1 : Rel.R n1) (S2 : Rel.R n2),
    R1 ~= S1 -> R2 ~= S2 -> Rel.times R1 R2 ~= Rel.times S1 S2.
  Proof.
    rewrite e1, e2. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma p_ext_dep m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n),
      (forall r1 r2, r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2) -> S1 ~= S2.
  Proof.
    rewrite e. intros. apply eq_JMeq. apply Rel.p_ext. 
    intro. apply H. reflexivity.
  Qed.

  Lemma eq_T_eqb_iff {m} {n} (t1 t2 : Rel.T m) (t3 t4 : Rel.T n) : 
    (t1 = t2 <-> t3 = t4) -> Rel.T_eqb t1 t2 = Rel.T_eqb t3 t4.
  Proof.
    destruct (Rel.T_eqb t1 t2) eqn:e1; destruct (Rel.T_eqb t3 t4) eqn:e2; intuition; auto.
    + rewrite <- e2. symmetry. apply Rel.T_eqb_eq. apply H0. apply Rel.T_eqb_eq. exact e1.
    + rewrite <- e1. apply Rel.T_eqb_eq. apply H1. apply Rel.T_eqb_eq. exact e2.
  Qed.

  Lemma sum_ext m n R (f g : Rel.T m -> Rel.T n) : 
    (forall x, f x = g x) -> Rel.sum R f = Rel.sum R g.
  Proof.
    intro. apply Rel.p_ext. intro.
    do 2 rewrite Rel.p_sum. repeat f_equal. extensionality x.
    destruct (Rel.T_eqb (g x) t) eqn:e; rewrite <- H in e; exact e.
  Qed.

  Lemma memb_sum_tech {m} {n} (R : Rel.R m) (f : Rel.T m -> Rel.T n) l1 : 
    NoDup l1 -> forall l2, incl l2 (Rel.supp R) -> NoDup l2 -> 
    (forall t u, List.In t l1 -> List.In u (Rel.supp R) -> f u = t -> List.In u l2) ->
    (forall u, List.In u l2 -> List.In (f u) l1) ->
    list_sum (List.map (Rel.memb (Rel.sum R f)) l1) = list_sum (List.map (Rel.memb R) l2).
  Proof.
    elim l1.
    + intros. replace l2 with (@List.nil (Rel.T m)). reflexivity.
      destruct l2; auto. contradiction (H3 t). left. reflexivity.
    + intros t l1' IH Hl1' l2 Hsupp Hl2 H1 H2. simpl.
      replace (list_sum (List.map (Rel.memb R) l2)) with
        (list_sum (List.map (Rel.memb R) (filter (fun x => Rel.T_eqb (f x) t) l2)) +
         list_sum (List.map (Rel.memb R) (filter (fun x => negb (Rel.T_eqb (f x) t)) l2))).
      - f_equal.
        * rewrite Rel.p_sum. apply (list_sum_ext Nat.eq_dec).
          generalize (Rel.p_nodup _ R) l2 Hsupp Hl2 H1; clear l2 Hsupp Hl2 H1 H2; elim (Rel.supp R).
          ++ simpl. intros _ l2 Hincl. replace l2 with (@List.nil (Rel.T m)). reflexivity.
             destruct l2; auto. contradiction (Hincl t0). left. reflexivity.
          ++ intros x l3' IHin Hnodup l2 Hincl Hl2 H1 y. simpl. destruct (Rel.T_eqb (f x) t) eqn:Heq; simpl.
            -- destruct (Nat.eq_dec (Rel.memb R x) y); simpl.
              ** assert (exists n, count_occ Nat.eq_dec 
                    (List.map (Rel.memb R) (filter (fun x0 : Rel.T m => Rel.T_eqb (f x0) t) l2)) y = S n).
                  apply count_occ_In_Sn. rewrite <- e. apply in_map. apply filter_In. split; auto.
                  eapply H1. left. reflexivity. left. reflexivity. apply Rel.T_eqb_eq. exact Heq.
                destruct H. rewrite (count_occ_rmone_r _ _ _ _ _ H). f_equal.
                transitivity (count_occ Nat.eq_dec (List.map (Rel.memb R) 
                  (filter (fun x1 => Rel.T_eqb (f x1) t) (rmone _ (Rel.T_dec _) x l2))) y).
                +++ apply IHin.
                  --- inversion Hnodup. exact H4.
                  --- eapply incl_rmone; assumption.
                  --- apply nodup_rmone. exact Hl2.
                  --- intros. apply in_rmone_neq. 
                    *** inversion Hnodup. intro. rewrite H8 in H6. contradiction H6.
                    *** eapply H1. exact H0. right. exact H2. exact H3.
                +++ apply map_filter_tech. exact Heq. rewrite e. reflexivity. 
                    eapply H1. left. reflexivity. left. reflexivity. apply Rel.T_eqb_eq. exact Heq.
              ** replace (count_occ Nat.eq_dec (List.map (Rel.memb R) (filter (fun x0 => Rel.T_eqb (f x0) t) l2)) y)
                  with (count_occ Nat.eq_dec (List.map (Rel.memb R) (filter (fun x0 => Rel.T_eqb (f x0) t) (rmone _ (Rel.T_dec _) x l2))) y).
                apply IHin.
                +++ inversion Hnodup. exact H3.
                +++ eapply incl_rmone; assumption.
                +++ apply nodup_rmone. exact Hl2. 
                +++ intros. apply in_rmone_neq. 
                  --- inversion Hnodup. intro. rewrite H7 in H5. contradiction H5.
                  --- eapply H1. exact H. right. exact H0. exact H2.
                +++ apply count_occ_map_filter_rmone_tech. exact n0.
            -- replace (count_occ Nat.eq_dec (List.map (Rel.memb R) (filter (fun x0 => Rel.T_eqb (f x0) t) l2)) y)
                  with (count_occ Nat.eq_dec (List.map (Rel.memb R) (filter (fun x0 => Rel.T_eqb (f x0) t) (rmone _ (Rel.T_dec _) x l2))) y). apply IHin.
              *** inversion Hnodup. exact H3.
              *** eapply incl_rmone; assumption.
              *** apply nodup_rmone. exact Hl2. 
              *** intros. apply in_rmone_neq. 
                +++ inversion Hnodup. intro. rewrite H7 in H5. contradiction H5.
                +++ eapply H1. exact H. right. exact H0. exact H2.
              *** rewrite filter_rmone_false. reflexivity. exact Heq.
        * apply IH.
          ++ inversion Hl1'; assumption.
          ++ intro x. intro Hx. apply Hsupp. 
             destruct (proj1 (filter_In (fun x => negb (Rel.T_eqb (f x) t)) x l2) Hx). exact H.
          ++ apply NoDup_filter. exact Hl2.
          ++ intros. apply filter_In. split.
            -- eapply H1. right. exact H. exact H0. exact H3.
            -- apply Bool.negb_true_iff. destruct (Rel.T_dec _ (f u) t).
              ** inversion Hl1'. rewrite <- e in H6. rewrite H3 in H6. contradiction H6.
              ** destruct (Rel.T_eqb (f u) t) eqn:ed; auto. contradiction n0. apply Rel.T_eqb_eq. exact ed.
          ++ intros. assert (List.In u l2 /\ negb (Rel.T_eqb (f u) t) = true).
            -- apply (proj1 (filter_In (fun x => negb (Rel.T_eqb (f x) t)) u l2) H).
            -- destruct H0. assert (f u <> t). intro. 
              pose (H4' := proj2 (Rel.T_eqb_eq _ (f u) t) H4); clearbody H4'.
              rewrite H4' in H3. discriminate H3. 
              pose (H2' := H2 _ H0); clearbody H2'. inversion H2'; auto. contradiction H4. symmetry. exact H5.
      - elim l2; auto.
        intros x l2' IHin. simpl. destruct (Rel.T_eqb (f x) t); simpl.
        * rewrite <- IHin. omega.
        * rewrite <- IHin. omega.
  Qed.

  Lemma card_sum : forall m n (f : Rel.T m -> Rel.T n) S, Rel.card (Rel.sum S f) = Rel.card S.
  Proof.
    intros. unfold Rel.card. do 2 rewrite Rel.p_sum.
    rewrite filter_true. rewrite filter_true.
    + apply memb_sum_tech.
      - apply Rel.p_nodup.
      - apply incl_refl.
      - apply Rel.p_nodup.
      - intros. exact H0.
      - intros. assert (Rel.memb (Rel.sum S f) (f u) > 0). 
        * rewrite Rel.p_sum. rewrite (count_occ_list_sum Nat.eq_dec (Rel.memb S u)).
          ++ apply lt_plus_trans. apply Rel.p_fs_r. exact H.
          ++ apply count_occ_In. apply in_map. apply filter_In; split; auto.
            apply Rel.T_eqb_eq. reflexivity.
        * apply Rel.p_fs. exact H0.
    + intros. apply Rel.T_eqb_eq. reflexivity.
    + intros. apply Rel.T_eqb_eq. reflexivity.
  Qed.

  Lemma Rel_times_Rone n (r : Rel.R n) : Rel.times r Rel.Rone ~= r.
  Proof.
    apply p_ext_dep. omega.
    intros t1 t2 et1t2.
    enough (forall t0, t1 = append t2 t0 -> Rel.memb (Rel.times r Rel.Rone) t1 = Rel.memb r t2).
    apply (H (Vector.nil _)). symmetry. apply JMeq_eq. apply (JMeq_trans (vector_append_nil_r _)).
    symmetry. exact et1t2.
    intros. rewrite H. rewrite (Rel.p_times _ _ _ _ _ _ _ eq_refl).
    eapply (case0 (fun x => Rel.memb r t2 * Rel.memb Rel.Rone x = Rel.memb r t2) _ t0). Unshelve. simpl. rewrite Rel.p_one. omega.
  Qed.

  Lemma Rel_sum_sum n1 n2 n3 (r : Rel.R n1) 
    (f : Rel.T n1 -> Rel.T n2) (g : Rel.T n2 -> Rel.T n3) 
    : Rel.sum (Rel.sum r f) g = Rel.sum r (fun x => g (f x)).
  Proof.
    apply Rel.p_ext. intro.
    repeat rewrite Rel.p_sum. apply memb_sum_tech.
    + apply NoDup_filter. apply Rel.p_nodup.
    + unfold incl. intros. destruct (proj1 (filter_In _ _ _) H). exact H0.
    + apply NoDup_filter. apply Rel.p_nodup.
    + intros. apply filter_In. destruct (proj1 (filter_In _ _ _) H). split; intuition.
      rewrite H1. exact H3.
    + intros. apply filter_In. destruct (proj1 (filter_In _ _ _) H). split; intuition.
      assert (Rel.memb (Rel.sum r f) (f u) > 0). 
        * rewrite Rel.p_sum. rewrite (count_occ_list_sum Nat.eq_dec (Rel.memb r u)).
          ++ apply lt_plus_trans. apply Rel.p_fs_r. exact H0.
          ++ apply count_occ_In. apply in_map. apply filter_In; split; auto.
            apply Rel.T_eqb_eq. reflexivity.
        * apply Rel.p_fs. exact H2.
  Qed.

  Lemma eq_sum_dep m1 m2 n1 n2 (e1 : m1 = m2) (e2 : n1 = n2) :
    forall (r1 : Rel.R m1) (r2 : Rel.R m2) (f : Rel.T m1 -> Rel.T n1) (g : Rel.T m2 -> Rel.T n2),
    r1 ~= r2 -> f ~= g -> Rel.sum r1 f ~= Rel.sum r2 g.
  Proof.
    rewrite e1, e2. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma eq_sel_dep m n (e : m = n) :
    forall (r1 : Rel.R m) (r2 : Rel.R n) (p : Rel.T m -> bool) (q : Rel.T n -> bool),
    r1 ~= r2 -> p ~= q -> Rel.sel r1 p ~= Rel.sel r2 q.
  Proof.
    rewrite e. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma sel_true {n} (S : Rel.R n) p : (forall r, List.In r (Rel.supp S) -> p r = true) -> Rel.sel S p = S.
  Proof.
    intro. apply Rel.p_ext. intro. destruct (p t) eqn:ept.
    + rewrite Rel.p_selt; auto.
    + rewrite Rel.p_self; auto. destruct (Rel.memb S t) eqn:eSt; auto.
      erewrite H in ept. discriminate ept.
      apply Rel.p_fs. rewrite eSt. omega.
  Qed.

  Lemma eq_memb_dep_elim1 : forall (P : nat -> Prop) m n (S1:Rel.R m) (S2 : Rel.R n) r2,
    m = n -> S1 ~= S2 ->
    (forall r1, r1 ~= r2 -> P (Rel.memb S1 r1)) ->
    P (Rel.memb S2 r2).
  Proof.
    intros. generalize S1, H0, H1. clear S1 H0 H1. 
    rewrite H. intros. rewrite <- H0.
    apply H1. reflexivity.
  Qed.

  Lemma sum_ext_dep m1 m2 n1 n2 R1 R2 (f : Rel.T m1 -> Rel.T m2) (g : Rel.T n1 -> Rel.T n2) : 
    m1 = n1 -> m2 = n2 -> R1 ~= R2 -> (forall x y, x ~= y -> f x ~= g y) -> Rel.sum R1 f ~= Rel.sum R2 g.
  Proof.
    intros. subst. rewrite H1. apply eq_JMeq. apply Rel.p_ext. intro.
    do 2 rewrite Rel.p_sum. repeat f_equal. extensionality x.
    rewrite (H2 x x). reflexivity. reflexivity.
  Qed.

  Lemma sum_ext_dep_elim1 m1 m2 n1 n2 f1 f2 (R2 : Rel.R m2) (P: forall n, Rel.R n -> Prop) : 
    m1 = m2 -> n1 = n2 -> f1 ~= f2 ->
    (forall (R1 : Rel.R m1), R1 ~= R2 -> P n1 (Rel.sum R1 f1)) ->
    P n2 (Rel.sum R2 f2).
  Proof.
    intros; subst. rewrite <- H1. apply H2. reflexivity.
  Qed.

  Lemma filter_supp_eq_tech n (al : list (Rel.T n)) x (Hal : NoDup al) :
    (List.In x al -> filter (fun x0 => Rel.T_eqb x0 x) al = x::List.nil)
    /\ (~List.In x al -> filter (fun x0 => Rel.T_eqb x0 x) al = List.nil).
  Proof.
    induction Hal.
    + split; intro.
      contradiction H. reflexivity.
    + destruct IHHal. split; intro.
      - inversion H2. simpl. replace (Rel.T_eqb x0 x) with true.
        rewrite H3. f_equal. apply H1. rewrite <- H3. exact H.
        symmetry. apply Rel.T_eqb_eq. exact H3.
        simpl. replace (Rel.T_eqb x0 x) with false. apply H0. exact H3.
        destruct (Rel.T_eqb x0 x) eqn:e; intuition. replace x with x0 in H3. contradiction H.
        apply Rel.T_eqb_eq. exact e.
      - simpl. replace (Rel.T_eqb x0 x) with false. apply H1. intro. apply H2. right. exact H3.
        destruct (Rel.T_eqb x0 x) eqn:e; intuition. replace x with x0 in H2. contradiction H2. left. reflexivity.
        apply Rel.T_eqb_eq. exact e.
  Qed.

  Lemma filter_supp_elim n R r (P : list (Rel.T n) -> Prop) :
    (List.In r (Rel.supp R) -> P (r::List.nil)) ->
    (~ List.In r (Rel.supp R) -> P List.nil) ->
    P (filter (fun (x0 : Rel.T n) => Rel.T_eqb x0 r) (Rel.supp R)).
  Proof.
    destruct (filter_supp_eq_tech _ (Rel.supp R) r (Rel.p_nodup _ R)).
    destruct (List.in_dec (Rel.T_dec _) r (Rel.supp R)); intros.
    rewrite H. apply H1. exact i. exact i.
    rewrite H0. apply H2. exact n0. exact n0.
  Qed.

  Lemma filter_supp_elim' m n R r (P : list (Rel.T (m+n)) -> Prop) :
    (List.In (flip r) (Rel.supp R) -> P (flip r::List.nil)) ->
    (~ List.In (flip r) (Rel.supp R) -> P List.nil) ->
    P (filter (fun x0 => Rel.T_eqb (flip x0) r) (Rel.supp R)).
  Proof.
    replace (fun x0 => Rel.T_eqb (flip x0) r) with (fun x0 => Rel.T_eqb x0 (flip r)). apply filter_supp_elim. 
    extensionality x0. apply eq_T_eqb_iff. split; intro.
    + symmetry. apply flip_inv. symmetry. exact H.
    + apply flip_inv. exact H.
  Qed.

  Lemma p_ext' : 
    forall m n, forall e : m = n, forall r : Rel.R m, forall s : Rel.R n, 
      (forall t, Rel.memb r t = Rel.memb s (eq_rect _ _ t _ e)) -> r ~= s.
  intros m n e. rewrite e. simpl.
  intros. rewrite (Rel.p_ext n r s). constructor. exact H.
  Qed.

  Lemma eq_sel m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n) p q,
    (forall r1 r2, r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2) ->
    (forall r1 r2, r1 ~= r2 -> p r1 = q r2) -> 
    Rel.sel S1 p ~= Rel.sel S2 q.
  Proof.
    rewrite e. intros.
    apply eq_JMeq. f_equal.
    + apply Rel.p_ext. intro. apply H. reflexivity.
    + extensionality r. apply H0. reflexivity.
  Qed.

  Lemma eq_card_dep m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n),
    S1 ~= S2 -> Rel.card S1 = Rel.card S2.
  Proof.
    rewrite e. intros. rewrite H. reflexivity.
  Qed.

  Lemma pred_impl_fs_sel n S p q :
    (forall (t : Rel.T n), p t = true -> q t = true) ->
    forall x, Rel.memb (Rel.sel S p) x <= Rel.memb (Rel.sel S q) x.
  Proof.
    intros Hpq x. destruct (p x) eqn:ep.
    + rewrite (Rel.p_selt _ _ _ _ ep). rewrite (Rel.p_selt _ _ _ _ (Hpq _ ep)). reflexivity.
    + rewrite (Rel.p_self _ _ _ _ ep). intuition.
  Qed.

End Facts.
