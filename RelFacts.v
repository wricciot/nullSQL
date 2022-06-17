(* if we do not remove the dependency on Syntax, we can't compile this until we fix syntax *)

Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Bool.Sumbool JMeq Common Syntax
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Syntax AbstractRelation Util.

Module Facts (Sql : SQL).

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

  Lemma eq_rsum_dep : forall m1 m2 n1 n2 : nat,
       m1 = m2 ->
       n1 = n2 ->
       forall (r1 : Rel.R m1) (r2 : Rel.R m2) (f : Rel.T m1 -> Rel.R n1) (g : Rel.T m2 -> Rel.R n2),
       r1 ~= r2 -> f ~= g -> Rel.rsum r1 f ~= Rel.rsum r2 g.
  Proof.
    intros; subst. rewrite H1, H2. reflexivity.
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

  Lemma sel_false {n} (S : Rel.R n) p : (forall r, List.In r (Rel.supp S) -> p r = false) -> Rel.sel S p = Rel.Rnil.
  Proof.
    intro. apply Rel.p_ext. intro. rewrite Rel.p_nil. destruct (p t) eqn:ept.
    + rewrite Rel.p_selt; auto. destruct (Rel.memb S t) eqn:eSt; auto.
      erewrite H in ept. discriminate ept. 
      apply Rel.p_fs. rewrite eSt. omega.
    + rewrite Rel.p_self; auto.
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

(*******)

  Lemma sum_id : forall m n (f : Rel.T m -> Rel.T n) r,
     m = n ->
     (forall x, f x ~= x) ->
     Rel.sum r f ~= r.
  Proof.
    intros. subst. apply eq_JMeq. eapply Rel.p_ext.
    intros v. rewrite Rel.p_sum.
    replace (fun x => Rel.T_eqb (f x) v) with (fun v' => Rel.T_eqb v' v).
    eapply filter_supp_elim; simpl; intro.
    + omega.
    + destruct (or_eq_lt_n_O (Rel.memb r v)); intuition.
      contradiction H. apply Rel.p_fs. exact H1.
    + extensionality v'. rewrite H0. reflexivity.
  Qed.

  Lemma rsum_id : forall m n (f : Rel.T m -> Rel.R n) r,
     m = n ->
     (forall x, f x ~= Rel.Rsingle x) ->
     Rel.rsum r f ~= r.
  Proof.
    intros. enough (exists (g : Rel.T m -> Rel.T n), forall x, g x ~= x).
    decompose record H1. rename x into g; rename H2 into Hg. clear H1.
    eapply (trans_JMeq _ (sum_id _ _ _ _ H Hg)). Unshelve.
      subst. exists (fun x => x); intuition.
    apply eq_JMeq; apply Rel.p_ext. intro.
    rewrite Rel.p_rsum. rewrite Rel.p_sum.
    induction (Rel.supp r); intuition.
    simpl. subst. rewrite H0, Hg, IHl.
    destruct (Rel.T_dec _ a t).
    + rewrite e, (proj2 (Rel.T_eqb_eq _ _ _) eq_refl), Rel.p_single. simpl. omega.
    + enough (Rel.T_eqb a t = false). rewrite H, Rel.p_single_neq. omega.
      exact n0. destruct (Rel.T_eqb a t) eqn:e. contradiction n0. apply (proj1 (Rel.T_eqb_eq _ _ _)). exact e.
      reflexivity.
  Qed.

  Lemma Rel_Rone_times n (r : Rel.R n) : Rel.times Rel.Rone r ~= r.
  Proof.
    apply p_ext_dep. omega.
    intros t1 t2 et1t2.
    enough (forall t0, t1 = append t0 t2 -> Rel.memb (Rel.times Rel.Rone r) t1 = Rel.memb r t2).
    apply (H (Vector.nil _)). symmetry. apply JMeq_eq.
    symmetry. exact et1t2.
    intros. rewrite H. rewrite (Rel.p_times _ _ _ _ _ _ _ eq_refl).
    eapply (case0 (fun x => Rel.memb Rel.Rone x * Rel.memb r t2 = Rel.memb r t2) _ t0). Unshelve. simpl. rewrite Rel.p_one. omega.
  Qed.

  (* maybe derive from another result: R_sum r (fun Vl => R_single x) = R.sum r (fun Vl => x). *)
  Lemma rsum_single : forall n (r : Rel.R n), Rel.rsum r (fun Vl => Rel.Rsingle Vl) ~= r.
  Proof.
    intros. apply rsum_id; intuition.
  Qed.

(*
  Lemma memb_sum_tech_r {m} {n} (R : Rel.R m) (f : Rel.T m -> Rel.T n) x l1 : 
    NoDup l1 -> forall l2, incl l2 (Rel.supp R) -> NoDup l2 -> 
    (forall t u, List.In t l1 -> List.In u (Rel.supp R) -> List.In t (Rel.supp (f u)) -> List.In u l2) ->
    (forall u, List.In u l2 -> List.Incl (Rel.supp (f u)) l1) ->
    list_sum (List.map (fun t => Rel.memb (Rel.rsum R f) t * Rel.memb (g t) x) l1) 
    = list_sum (List.map (fun u => Rel.memb R u * Rel.memb (Rel.rsum (f t) g) x) l2).
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

*)

  Lemma list_sum_plus {A} (f g : A -> nat) l :
    list_sum (List.map (fun x => f x + g x) l) = list_sum (List.map f l) + list_sum (List.map g l).
  Proof.
    induction l; intuition.
    simpl. rewrite IHl. omega.
  Qed.

  Lemma list_sum_times_l {A} n (f : A -> nat) l :
    list_sum (List.map (fun x => n * f x) l) = n * list_sum (List.map f l).
  Proof.
    induction l; intuition.
    simpl. rewrite IHl. rewrite mult_plus_distr_l. reflexivity.
  Qed.

  Lemma list_sum_append l1 l2 : list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
  Proof.
    induction l1; simpl; intuition.
  Qed.

  Lemma NoDup_remove {A} (a:A) l1 l2 : NoDup (l1 ++ a :: l2) -> NoDup (l1 ++ l2).
  Proof.
    induction l1; simpl; intros.
    + inversion H; intuition.
    + constructor. inversion H. intro; apply H2.
      apply in_or_app. destruct (in_app_or _ _ _ H4).
      left; assumption. right; right; assumption.
      apply IHl1. inversion H. intuition.
  Qed.

  Lemma rsum_rsum_list_sum {A} (l1 l2 : list A) f:
    NoDup l1 -> NoDup l2 -> incl l2 l1 ->
    (forall x, List.In x l1 -> ~ List.In x l2 -> f x = 0) ->
    list_sum (List.map f l1) = list_sum (List.map f l2).
  Proof.
    intros. generalize dependent l1; induction l2.
    + induction l1; simpl; intuition. rewrite H2. apply IHl1. inversion H; intuition.
      intro. intro. inversion H3.
      intros. apply H2; intuition. left. reflexivity.
      intro. inversion H3.
    + simpl. intros. enough (List.In a l1). decompose record (in_split _ _ H3). rewrite H5.
      rewrite map_app, list_sum_append. simpl.
      rewrite (plus_comm (f a)). rewrite plus_assoc. rewrite <- list_sum_append, <- map_app.
      rewrite plus_comm. f_equal. apply IHl2.
      - inversion H0; intuition.
      - rewrite H5 in H. apply (NoDup_remove _ _ _ H).
      - enough (forall A (y z : A) la lb lc, List.In y la -> y <> z -> incl la (lb ++ z :: lc) -> List.In y (lb ++ lc)).
        intro. intro. eapply (H4 _ a0 a). apply H6. inversion H0; intro; subst. contradiction H9.
        intro. intro. enough (List.In a1 (a::l2)).
        generalize (H1 _ H8). rewrite H5; intuition.
        right; exact H7.
        intros B y z la. induction la; simpl; intros. contradiction H4.
        destruct H4. subst. enough (List.In y (lb ++ z :: lc)).
        induction lb in H4 |- *; simpl. simpl in H4. destruct H4; subst; intuition.
        simpl in H4. destruct H4. intuition. right. apply IHlb. exact H4.
        apply H7. left; reflexivity.
        apply IHla. exact H4. exact H6. intro. intro. apply H7. right. exact H8.
      - intros. apply H2. rewrite H5. apply in_or_app. destruct (in_app_or _ _ _  H4).
        left; exact H7. right; right; exact H7.
        intro. destruct H7. subst. induction x in H, H4, H3. inversion H. contradiction H5. 
        apply IHx. simpl in H; inversion H; exact H7.
        apply in_or_app; right; left; reflexivity.
        inversion H4. rewrite H1 in H. inversion H. contradiction H7. apply in_or_app; right; left; reflexivity.
        exact H1.
        contradiction H6.
      - apply H1. left; reflexivity.
  Qed.

  Lemma incl_supp_rsum {m n} a (r : Rel.R m) (f : Rel.T m -> Rel.R n) : 
    List.In a (Rel.supp r) -> incl (Rel.supp (f a)) (Rel.supp (Rel.rsum r f)).
  Proof.
    repeat intro. apply Rel.p_fs. rewrite Rel.p_rsum.
    generalize (Rel.p_fs_r _ _ _ H0). intro.
    decompose record (in_split _ _ H). rewrite H3. 
    rewrite map_app, list_sum_append.
    replace (list_sum (List.map (fun t0 => Rel.memb r t0 * Rel.memb (f t0) a0) (a :: x0)))
       with (Rel.memb r a * Rel.memb (f a) a0 + list_sum (List.map (fun t0 => Rel.memb r t0 * Rel.memb (f t0) a0) x0)).
    2: { reflexivity. }
    rewrite plus_assoc. rewrite plus_comm. rewrite plus_assoc. change 0 with (0 + 0).
    apply plus_le_lt_compat. omega.
    unfold lt. change 1 with (1*1). apply mult_le_compat.
    apply Rel.p_fs_r. exact H.
    apply Rel.p_fs_r. exact H0.
  Qed.

  Lemma rsum_rsum_tech {m n o} (r : Rel.R m) (f : Rel.T m -> Rel.R n) (g : Rel.T n -> Rel.R o) (t : Rel.T o)
    : forall l, incl l (Rel.supp r) ->
      list_sum (List.map (fun x =>
        list_sum (List.map (fun y => 
          Rel.memb r y * Rel.memb (f y) x) l)
          * Rel.memb (g x) t) (Rel.supp (Rel.rsum r f))) 
      = list_sum (List.map (fun z =>
          Rel.memb r z * list_sum (List.map (fun w => 
            Rel.memb (f z) w * Rel.memb (g w) t) (Rel.supp (f z)))) l).
  Proof.
    induction l; simpl. induction (Rel.supp (Rel.rsum r f)); intuition. intro.
    transitivity
      (list_sum (List.map (fun x =>
        Rel.memb r a * Rel.memb (f a) x * Rel.memb (g x) t
        + list_sum (List.map (fun y : Rel.T m => Rel.memb r y * Rel.memb (f y) x) l) * Rel.memb (g x) t)
        (Rel.supp (Rel.rsum r f)))).
    1: { f_equal. f_equal. extensionality x. rewrite mult_plus_distr_r. reflexivity. }
    rewrite (list_sum_plus (fun x => Rel.memb r a * Rel.memb (f a) x * Rel.memb (g x) t)
      (fun x => list_sum (List.map (fun y => Rel.memb r y * Rel.memb (f y) x) l) * Rel.memb (g x) t)).
    rewrite IHl. f_equal.
    transitivity (list_sum (List.map (fun x => 
      Rel.memb r a * (Rel.memb (f a) x * Rel.memb (g x) t)) (Rel.supp (Rel.rsum r f)))).
    1: { f_equal. f_equal. extensionality x. rewrite mult_assoc. reflexivity. }
    rewrite (list_sum_times_l (Rel.memb r a) (fun x => Rel.memb (f a) x * Rel.memb (g x) t)).
    f_equal.
    apply rsum_rsum_list_sum. apply Rel.p_nodup. apply Rel.p_nodup.
    apply incl_supp_rsum. apply H. left; reflexivity. 
    intros. replace (Rel.memb (f a) x) with 0. omega.
    destruct (or_eq_lt_n_O (Rel.memb (f a) x)). omega.
    generalize (Rel.p_fs _ _ _ H2). intro. contradiction H1.
    repeat intro. apply H. right. exact H0.
  Qed.

  Lemma rsum_rsum {m n o} (r : Rel.R m) (f : Rel.T m -> Rel.R n) (g: Rel.T n -> Rel.R o) 
    : Rel.rsum (Rel.rsum r f) g = Rel.rsum r (fun x => Rel.rsum (f x) g).
  Proof.
    apply Rel.p_ext; intro.
    repeat rewrite Rel.p_rsum.
    transitivity 
      (list_sum (List.map (fun x => 
         list_sum (List.map (fun y => 
           Rel.memb r y * Rel.memb (f y) x) (Rel.supp r)) 
         * Rel.memb (g x) t) (Rel.supp (Rel.rsum r f)))).
    1: { f_equal. f_equal. extensionality x. rewrite Rel.p_rsum. reflexivity. }
    transitivity
      (list_sum (List.map (fun z => Rel.memb r z * 
       list_sum (List.map (fun w => Rel.memb (f z) w * Rel.memb (g w) t) (Rel.supp (f z)))) (Rel.supp r))).
    2: { f_equal. f_equal. extensionality z. rewrite Rel.p_rsum. reflexivity. }
    apply rsum_rsum_tech.
    apply incl_refl.
  Qed.

  Lemma sel_rsum {m n} (r : Rel.R m) (p : Rel.T n -> bool) (f : Rel.T m -> Rel.R n)
    : Rel.sel (Rel.rsum r f) p = Rel.rsum r (fun x => (Rel.sel (f x) p)).
  Proof.
    apply Rel.p_ext; intro. destruct (p t) eqn:ep.
    + rewrite Rel.p_selt. repeat rewrite Rel.p_rsum.
      induction (Rel.supp r); intuition.
      simpl. rewrite Rel.p_selt. intuition. exact ep. exact ep.
    + rewrite Rel.p_self. rewrite Rel.p_rsum. induction (Rel.supp r); intuition.
      simpl. rewrite IHl, Rel.p_self. omega. exact ep. exact ep.
  Qed.

  Lemma eq_sum_rsum {m n} r (f : Rel.T m -> Rel.T n) : Rel.sum r f = Rel.rsum r (fun x => Rel.Rsingle (f x)).
  Proof.
    apply Rel.p_ext; intro. rewrite Rel.p_sum, Rel.p_rsum. induction (Rel.supp r); intuition.
    simpl. destruct (Rel.T_dec _ (f a) t).
    + rewrite e, (proj2 (Rel.T_eqb_eq _ _ _) eq_refl), Rel.p_single. simpl. omega.
    + enough (Rel.T_eqb (f a) t = false). rewrite H, Rel.p_single_neq. omega.
      exact n0. destruct (Rel.T_eqb (f a) t) eqn:e. contradiction n0. apply (proj1 (Rel.T_eqb_eq _ _ _)). exact e.
      reflexivity.
  Qed.

  Lemma sel_times_single {m n} (r : Rel.R m) (x : Rel.T n) p : 
    Rel.sel (Rel.times r (Rel.Rsingle x)) p = Rel.times (Rel.sel r (fun Vl => p (append Vl x))) (Rel.Rsingle x).
  Proof.
    apply Rel.p_ext; intro. decompose record (exists_vector_append _ _ _ _ t eq_refl). destruct (p t) eqn:ep.
    + rewrite Rel.p_selt. 
      repeat rewrite (Rel.p_times _ _ _ _ _ _ _ (JMeq_eq H0)).
      destruct (Rel.T_dec _ x x1).
      - subst. rewrite Rel.p_selt. reflexivity. exact ep.
      - rewrite Rel.p_single_neq. omega. exact n0.
      - exact ep.
    + rewrite Rel.p_self. rewrite (Rel.p_times _ _ _ _ _ _ _ (JMeq_eq H0)).
      destruct (Rel.T_dec _ x x1).
      - subst. rewrite Rel.p_self. omega. exact ep.
      - rewrite Rel.p_single_neq. omega. exact n0.
      - exact ep.
  Qed.

(*********)

  Lemma filter_false A p (l : list A) : 
    (forall x, List.In x l -> p x = false) -> filter p l = List.nil.
  Proof.
    elim l. auto.
    intros h t IH Hp. simpl. rewrite Hp.
    + apply IH. intros. apply Hp. right. exact H.
    + left. reflexivity.
  Qed.

  Lemma sum_append : forall m n o (f : Rel.T m -> Rel.T n) r (t : Rel.T o),
     n = m + o ->
     (forall x, f x ~= append x t) ->
     Rel.sum r f ~= Rel.times r (Rel.Rsingle t).
  Proof.
    intros. subst. apply eq_JMeq. eapply Rel.p_ext.
    intros v. rewrite Rel.p_sum.
    replace (fun x => Rel.T_eqb (f x) v) with (fun v' => Rel.T_eqb (append v' t) v).
    decompose record (exists_vector_append _ _ _ _ v eq_refl). rename x into v1. rename x0 into v2.
    rewrite H1, (Rel.p_times _ _ _ _ _ v1 v2 eq_refl).
    destruct (Rel.T_dec _ t v2).
    + replace (fun v' => Rel.T_eqb (append v' t) (append v1 v2)) with (fun v' => Rel.T_eqb v' v1).
      rewrite e, Rel.p_single. eapply filter_supp_elim; simpl; intro.
      - omega.
      - destruct (or_eq_lt_n_O (Rel.memb r v1)); intuition.
        contradiction H. apply Rel.p_fs. exact H2.
      - extensionality v'. rewrite e. destruct (Rel.T_dec _ v' v1).
        rewrite (proj2 (Rel.T_eqb_eq _ _ _) e0); symmetry. apply (proj2 (Rel.T_eqb_eq _ _ _)).
        rewrite e0. reflexivity.
        replace (Rel.T_eqb v' v1) with false. symmetry.
        destruct (Rel.T_dec _ (append v' v2) (append v1 v2)). decompose record (vec_append_inj e0).
        contradiction (n H).
        destruct (Rel.T_eqb (append v' v2) (append v1 v2)) eqn:eapp.
        rewrite (proj1 (Rel.T_eqb_eq _ _ _) eapp) in n0. contradiction n0. reflexivity.
        reflexivity.
        symmetry. destruct (Rel.T_eqb v' v1) eqn:e0.
        rewrite (proj1 (Rel.T_eqb_eq _ _ _) e0) in n. contradiction n. reflexivity.
        reflexivity.
    + rewrite filter_false. replace (Rel.memb (Rel.Rsingle t) v2) with 0. simpl; omega.
      rewrite Rel.p_single_neq. reflexivity. exact n.
      intros v' Hv'. destruct (Rel.T_eqb (append v' t) (append v1 v2)) eqn:eapp.
      decompose record (vec_append_inj (proj1 (Rel.T_eqb_eq _ _ _) eapp)). contradiction n.
      reflexivity.
    + extensionality v'. rewrite H0. reflexivity.
  Qed.

  Lemma rsum_append : forall m n o (f : Rel.T m -> Rel.R n) r (t : Rel.T o),
     n = m + o ->
     (forall x, f x ~= Rel.Rsingle (append x t)) ->
     Rel.rsum r f ~= Rel.times r (Rel.Rsingle t).
  Proof.
    intros; subst. erewrite <- (sum_append _ _ _ (fun x => append x t)).
    rewrite eq_sum_rsum. replace f with (fun (x:Rel.T m) => Rel.Rsingle (append x t)).
    reflexivity. extensionality v. rewrite H0. reflexivity.
    reflexivity.
    intuition.
  Qed.

  Lemma supp_single_aux {A} (t : A) (l : list A) :
    (forall (x y:A), {x = y} + {x <> y}) ->
    List.In t l ->
    (forall u, t <> u -> ~ List.In u l) ->
    NoDup l ->
    l = t::List.nil.
  Proof.
    intros. destruct l.
    + inversion H.
    + destruct (X a t).
      - subst. destruct l; intuition.
        destruct (X a t); subst.
        inversion H1. contradiction H4. left. reflexivity.
        exfalso. apply (H0 a). intuition. right; left; reflexivity.
      - contradiction (H0 a). intuition. left; reflexivity.
  Qed.

  Lemma supp_single : forall n (t : Rel.T n), Rel.supp (Rel.Rsingle t) = t::List.nil.
  Proof.
    intros. apply supp_single_aux. apply (Rel.T_dec _).
    apply Rel.p_fs. rewrite Rel.p_single. omega.
    intros. intro. generalize (Rel.p_fs_r _ _ _ H0). rewrite Rel.p_single_neq. omega.
    assumption.
    apply Rel.p_nodup.
  Qed.

  Lemma rsum_from_single : forall m n t (f : Rel.T m -> Rel.R n), 
    Rel.rsum (Rel.Rsingle t) f = f t.
  Proof.
    intros. apply Rel.p_ext. intro. rewrite Rel.p_rsum.
    replace (Rel.supp (Rel.Rsingle t)) with (t::List.nil).
    simpl. rewrite Rel.p_single. omega.
    symmetry; apply supp_single.
  Qed.

  Lemma rsum_times_single {m n o} (r : Rel.R m) (x : Rel.T n) (f : Rel.T (m + n) -> Rel.R o) :
    Rel.rsum (Rel.times r (Rel.Rsingle x)) f = Rel.rsum r (fun Vl => f (append Vl x)).
  Proof.
    replace (Rel.times r (Rel.Rsingle x)) with (Rel.rsum r (fun v => Rel.Rsingle (append v x))).
    rewrite rsum_rsum. f_equal.
    extensionality Vl. apply rsum_from_single.
    apply JMeq_eq. apply rsum_append. reflexivity. intuition.
  Qed.

  Lemma flatnat_plus : forall x y, Rel.flatnat (x + y) = max (Rel.flatnat x) (Rel.flatnat y).
  Proof.
    intros. destruct x; destruct y; simpl; reflexivity.
  Qed.

  Lemma flatnat_times : forall x y, Rel.flatnat (x * y) = min (Rel.flatnat x) (Rel.flatnat y).
  Proof.
    intros. destruct x; destruct y; simpl; intuition.
    replace (x * 0) with 0. reflexivity. omega.
  Qed.

  Lemma flatnat_flatnat : forall x, Rel.flatnat (Rel.flatnat x) = Rel.flatnat x.
  Proof.
    intros. destruct x; reflexivity.
  Qed.

  Lemma flat_rsum_flat {m n} (r : Rel.R m) (fr : Rel.T m -> Rel.R n) : 
    Rel.flat (Rel.rsum r (fun Vl => Rel.flat (fr Vl))) = Rel.flat (Rel.rsum r (fun Vl => fr Vl)).
  Proof.
    apply Rel.p_ext; intro. repeat rewrite Rel.p_flat. repeat rewrite Rel.p_rsum.
    induction (Rel.supp r); intuition.
    simpl. repeat rewrite flatnat_plus. rewrite IHl. f_equal.
    rewrite Rel.p_flat. repeat rewrite flatnat_times. f_equal.
    apply flatnat_flatnat.
  Qed.

  Lemma flat_Rsingle n (v : Rel.T n) : Rel.flat (Rel.Rsingle v) = Rel.Rsingle v.
  Proof.
    apply Rel.p_ext; intros. rewrite Rel.p_flat.
    destruct (Rel.T_dec _ v t).
    + rewrite e. rewrite Rel.p_single. reflexivity.
    + rewrite Rel.p_single_neq; intuition.
  Qed.

  Lemma sum_Rone_Rsingle n (f : Rel.T 0 -> Rel.T n) : Rel.sum Rel.Rone f = Rel.Rsingle (f (Vector.nil _)).
  Proof.
    apply Rel.p_ext; intro. rewrite Rel.p_sum. replace (Rel.supp Rel.Rone) with (Vector.nil Rel.V ::List.nil).
    destruct (Rel.T_dec _ (f (nil _)) t).
    + rewrite e. rewrite Rel.p_single. 
      simpl. rewrite e. simpl. rewrite (proj2 (Rel.T_eqb_eq _ _ _) eq_refl). simpl. rewrite Rel.p_one. omega.
    + rewrite Rel.p_single_neq. simpl. destruct (Rel.T_eqb (f (nil _)) t) eqn:e; simpl; intuition.
      contradiction n0. apply Rel.T_eqb_eq. exact e. exact n0.
    + enough (forall x y z, Rel.supp Rel.Rone <> x::y::z).
      enough (Rel.supp Rel.Rone <> List.nil).
      destruct (Rel.supp Rel.Rone). contradiction H0. reflexivity.
      destruct l. eapply (Vector.case0 (fun x => _ = x :: _)). reflexivity.
      contradiction (H t0 t1 l). reflexivity.
      intro. enough (List.In (nil _) (Rel.supp Rel.Rone)). rewrite H0 in H1; exact H1.
      apply Rel.p_fs. rewrite Rel.p_one. omega.
      intros. intro. generalize (Rel.p_nodup _ Rel.Rone).
      rewrite H. eapply (Vector.case0 (fun a => NoDup (a :: _) -> False)).
      eapply (Vector.case0 (fun a => NoDup (_ :: a :: _) -> False)). intro.
      inversion H0. contradiction H3. simpl. left. reflexivity.
  Qed.

End Facts.