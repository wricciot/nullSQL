Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Bool.Sumbool JMeq Common
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Syntax Eval Util Tribool.

Module Facts.

  Import Db.

  Module S2 := Sem2.
  Module S3 := Sem3.

  Lemma projT1_env_app G1 G2 h1 h2 : 
    projT1 (Evl.env_app G1 G2 h1 h2) = projT1 h1 ++ projT1 h2.
  Proof.
    destruct h1. destruct h2. reflexivity.
  Qed.

  Lemma projT1_env_of_tuple G x : 
    projT1 (Evl.env_of_tuple G x) = to_list x.
  Proof.
    induction G.
    + simpl in x. eapply (case0 (fun v => List.nil = to_list v) _ x). Unshelve. reflexivity.
    + simpl. simpl in x. 
      enough (forall v1 v2, x = append v1 v2 -> 
        to_list v1 ++ projT1 (Evl.env_of_tuple G v2) = to_list x).
      erewrite <- (H (fst (split x)) (snd (split x))). reflexivity.
      apply JMeq_eq.
      apply (split_ind x (fun m n p => x ~= append (fst p) (snd p))).
      intros. rewrite H0. reflexivity.
      intros. rewrite H. rewrite to_list_append. f_equal. apply IHG.
  Qed.

  Lemma subenv1_app : forall G1 G2 h1 h2, Evl.subenv1 (Evl.env_app G1 G2 h1 h2) = h1.
  Proof.
    intros. destruct h1. destruct h2. unfold Evl.env_app. simpl.
    destruct (Nat.eqb_eq (length (concat (G1 ++ G2))) (length (x ++ x0))).
    unfold Evl.subenv1. apply Evl.env_eq. simpl. replace (length (concat G1)) with (length x).
    rewrite firstn_app. replace (length x - length x) with O.
    replace x with (x ++ firstn 0 x0) at 3. f_equal.
    apply List.firstn_all. rewrite firstn_O. apply app_nil_r.
    omega.
    symmetry. apply Nat.eqb_eq. exact e.
  Qed.

  Lemma subenv2_app : forall G1 G2 h1 h2, Evl.subenv2 (Evl.env_app G1 G2 h1 h2) = h2.
  Proof.
    intros. destruct h1. destruct h2. unfold Evl.env_app. simpl.
    destruct (Nat.eqb_eq (length (concat (G1 ++ G2))) (length (x ++ x0))).
    unfold Evl.subenv2. apply Evl.env_eq. simpl. replace (length (concat G1)) with (length x).
    rewrite Evl.skipn_append. reflexivity.
    symmetry. apply Nat.eqb_eq. exact e.
  Qed.



  Lemma env_app_nil_l : forall G h1 h2, Evl.env_app List.nil G h1 h2 = h2.
  Proof.
    intros. apply Evl.env_eq. destruct h1. simpl. replace x with (@List.nil Rel.V). reflexivity.
    destruct x; intuition.
    simpl in e. discriminate e.
  Qed.

  Lemma env_hd_hd : forall a s G (h : Evl.env ((a::s)::G)) x, 
    List.hd_error (projT1 h) = Some x -> Evl.env_hd h = x.
  Proof.
    intros. enough (hd_error (projT1 h) <> None).
    destruct h. unfold Evl.env_hd.
    rewrite (Evl.unopt_pi _ _ H0). generalize dependent H0. rewrite H. intro. reflexivity.
    rewrite H. intro. discriminate H0.
  Qed.

  Lemma env_tl_tl : forall a s G (h : Evl.env ((a::s)::G)),
    projT1 (Evl.env_tl h) = List.tl (projT1 h).
  Proof.
    intros. destruct h. simpl. reflexivity.
  Qed.

  Lemma S2_is_btrue_and_intro (b1 b2 : bool) :
    S2.is_btrue b1 = true -> S2.is_btrue b2 = true ->
    S2.is_btrue (b1 && b2) = true.
  Proof.
    Bool.destr_bool.
  Qed.

  Lemma S2_is_btrue_and_elim (b1 b2 : bool) (P : Prop) :
    (S2.is_btrue b1 = true -> S2.is_btrue b2 = true -> P) ->
    S2.is_btrue (b1 && b2) = true -> P.
  Proof.
    Bool.destr_bool. auto.
  Qed.

  Lemma S3_is_btrue_and_intro (b1 b2 : tribool) :
    S3.is_btrue b1 = true -> S3.is_btrue b2 = true ->
    S3.is_btrue (b1 && b2) = true.
  Proof.
    destr_tribool.
  Qed.

  Lemma S3_is_btrue_and_elim (b1 b2 : tribool) (P : Prop) :
    (S3.is_btrue b1 = true -> S3.is_btrue b2 = true -> P) ->
    S3.is_btrue (b1 && b2) = true -> P.
  Proof.
    destr_tribool. auto.
  Qed.

  Lemma S2_is_btrue_and (b1 b2 : bool) :
    S2.is_btrue (b1 && b2) = ((S2.is_btrue b1)&&(S2.is_btrue b2))%bool.
  Proof.
    Bool.destr_bool.
  Qed.

  Lemma S3_is_btrue_and (b1 b2 : tribool) :
    S3.is_btrue (b1 && b2)%tribool = ((S3.is_btrue b1)&&(S3.is_btrue b2))%bool.
  Proof.
    destr_tribool.
  Qed.

  Lemma S2_is_btrue_or (b1 b2 : bool) :
    S2.is_btrue (b1 || b2) = ((S2.is_btrue b1)||(S2.is_btrue b2))%bool.
  Proof.
    Bool.destr_bool.
  Qed.

  Lemma S3_is_btrue_or (b1 b2 : tribool) :
    S3.is_btrue (b1 || b2) = ((S3.is_btrue b1)||(S3.is_btrue b2))%bool.
  Proof.
    destr_tribool.
  Qed.

  Lemma eqb_ort_ttrue (b1 b2 : tribool) :
    eqb (b1 || b2)%tribool ttrue = ((eqb b1 ttrue)||(eqb b2 ttrue))%bool.
  Proof.
    destr_tribool.
  Qed.

  Lemma S2_is_btrue_false_and1 (b1 b2 : bool) :
    S2.is_btrue b1 = false -> S2.is_btrue (b1 && b2) = false.
  Proof.
    Bool.destr_bool.
  Qed.

  Lemma S2_is_btrue_false_and2 (b1 b2 : bool) :
    S2.is_btrue b2 = false -> S2.is_btrue (b1 && b2) = false.
  Proof.
    Bool.destr_bool.
  Qed.

  Lemma S3_is_btrue_false_and1 (b1 b2 : tribool) :
    S3.is_btrue b1 = false -> S3.is_btrue (b1 && b2) = false.
  Proof.
    destr_tribool.
  Qed.

  Lemma S3_is_btrue_false_and2 (b1 b2 : tribool) :
    S3.is_btrue b2 = false -> S3.is_btrue (b1 && b2) = false.
  Proof.
    destr_tribool.
  Qed.

  Lemma p_eq_not_neq n vl wl :
    (fun ul => fold_right2 (fun u0 v0 acc => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul vl) wl = true
    ->
    (fun ul => fold_right2 (fun u0 v0 acc => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n ul vl) wl = true.
  Proof.
    simpl.
    eapply (Vector.rect2 (fun n0 vl0 wl0 => 
      fold_right2 (fun (u0 v0 : option BaseConst) (acc : bool) => 
        (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n0 wl0 vl0 = true ->
      fold_right2 (fun (u0 v0 : option BaseConst) (acc : bool) => 
        (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n0 wl0 vl0 = true) _ _ vl wl). Unshelve.
    + simpl. auto.
    + simpl. intros m vl0 wl0 IH v w. destruct (S3.veq w v); simpl.
      - destruct (fold_right2 (fun (u0 v0 : option BaseConst) (acc : bool) => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true m
         wl0 vl0) eqn:e; simpl.
        * intros _. rewrite IH; auto.
        * intro Hfalse; intuition.
      - destruct (fold_right2 (fun (u0 v0 : option BaseConst) (acc : bool) => acc && S3.is_btrue (S3.veq u0 v0))%bool true m wl0 vl0);
        simpl; intro Hfalse; intuition.
      - destruct (fold_right2 (fun (u0 v0 : option BaseConst) (acc : bool) => acc && S3.is_btrue (S3.veq u0 v0))%bool true m wl0 vl0);
        simpl; intro Hfalse; intuition.
  Qed.

  Lemma p_eq_not_neq_r n vl wl :
    (fun ul => fold_right2 (fun u0 v0 acc => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n ul vl) wl = false
    ->
    (fun ul => fold_right2 (fun u0 v0 acc => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul vl) wl = false.
  Proof.
    intros. destruct ((fun ul : t (option BaseConst) n => fold_right2 
      (fun (u0 v0 : option BaseConst) (acc : bool) => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul vl) 
      wl) eqn:e; auto.
    simpl in H. rewrite (p_eq_not_neq _ _ _ e) in H. discriminate H.
  Qed.

  Lemma le_memb_eq_not_neq n S vl wl:
         Rel.memb (Rel.sel S (fun ul : Rel.T n => fold_right2
             (fun (u0 v0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul vl)) wl
         <= Rel.memb (Rel.sel S (fun ul : Rel.T n => fold_right2
               (fun (u0 v0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n ul vl)) wl.
  Proof.
    pose (p := fun ul => fold_right2 (fun u0 v0 acc => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul vl).
    pose (q := fun ul => fold_right2 (fun u0 v0 acc => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n ul vl).
    destruct (p wl) eqn:ep.
    - cut (q wl = true).
      * intro eq. rewrite (Rel.p_selt _ _ _ _ ep). rewrite (Rel.p_selt _ _ _ _ eq). reflexivity.
      * generalize ep; clear ep. simpl. apply p_eq_not_neq.
    - rewrite (Rel.p_self _ _ _ _ ep). destruct (q wl) eqn:eq.
      * rewrite (Rel.p_selt _ _ _ _ eq). intuition.
      * rewrite (Rel.p_self _ _ _ _ eq). reflexivity.
  Qed.

  Lemma le_card_eq_not_neq n S vl:
         Rel.card (Rel.sel S (fun ul : Rel.T n => fold_right2
             (fun (u0 v0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul vl))
         <= Rel.card (Rel.sel S (fun ul : Rel.T n => fold_right2
               (fun (u0 v0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n ul vl)).
  Proof.
    unfold Rel.card. do 2 rewrite Rel.p_sum.
    rewrite filter_true; auto. rewrite filter_true; auto.
    * pose (p := fun ul0 => fold_right2 (fun u0 v0 acc => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul0 vl).
      pose (q := fun ul0 => fold_right2 (fun u0 v0 acc => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n ul0 vl).
      pose (Hp := Rel.p_nodup _ (Rel.sel S p)); clearbody Hp.
      pose (Hq := Rel.p_nodup _ (Rel.sel S q)); clearbody Hq.
      apply (le_list_sum_memb_tech _ (Rel.T_dec n)).
      + apply le_memb_eq_not_neq.
      + apply Rel.p_nodup.
      + apply Rel.p_nodup.
      + intros ul Hin Hmemb.
        pose (Hnodup := NoDup_count_occ (Rel.T_dec n) (Rel.supp (Rel.sel S p))); clearbody Hnodup.
        destruct Hnodup. clear H0.
        apply Rel.p_fs. unfold gt. unfold lt.
        transitivity (Rel.memb (Rel.sel S p) ul).
        - exact Hmemb.
        - apply le_memb_eq_not_neq.
    * intros. apply Rel.T_eqb_eq. reflexivity.
    * intros. apply Rel.T_eqb_eq. reflexivity.
  Qed.

  Lemma fold_right_not_neq_iff n (ul vl : Rel.T n) :
    fold_right2 (fun (u0 v0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool)
        true n ul vl = true
    <-> forall (i : Fin.t n), S3.is_bfalse (S3.veq (nth ul i) (nth vl i)) = false.
  Proof.
    eapply (rect2 (fun n0 ul0 vl0 => 
            fold_right2 (fun (u0 v0 : Value) (acc : bool) => 
              (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true n0 ul0 vl0 = true 
            <-> (forall (i0 : Fin.t n0), S3.is_bfalse (S3.veq (nth ul0 i0) (nth vl0 i0)) = false))
          _ _ ul vl). Unshelve.
    + simpl. split; auto. intros _ i. inversion i.
    + intros m ul0 vl0 IH u0 v0. split.
      - intros H i. 
        cut (forall ul1 vl1, 
          ul1 ~= cons Value u0 m ul0 -> vl1 ~= cons Value v0 m vl0 -> 
          S3.is_bfalse (S3.veq (nth ul1 i) (nth vl1 i)) = false).
        * intro Hcut. apply Hcut; reflexivity.
        * dependent inversion i with (fun p (i0 : Fin.t p) => forall ul1 vl1, 
          ul1 ~= cons Value u0 m ul0 -> vl1 ~= cons Value v0 m vl0 -> 
          S3.is_bfalse (S3.veq (nth ul1 i0) (nth vl1 i0)) = false).
          ++ intros. rewrite H0, H2. simpl in H. simpl. destruct (S3.veq u0 v0);auto.
             symmetry in H. destruct (Bool.andb_true_eq _ _ H).
             unfold S3.is_bfalse in H4. discriminate H4.
          ++ intros. rewrite H0, H2. simpl.
             apply IH. simpl in H. symmetry in H. destruct (Bool.andb_true_eq _ _ H).
             rewrite <- H3. reflexivity.
      - intro H. simpl. apply Bool.andb_true_iff. split.
        * apply IH. intro i. apply (H (Fin.FS i)).
        * apply Bool.negb_true_iff. apply (H Fin.F1).
  Qed.

  Lemma S2_is_btrue_or_elim (b1 b2 : bool) (P : Prop) :
    (S2.is_btrue b1 = true -> P) -> (S2.is_btrue b2 = true -> P) ->
    S2.is_btrue (b1 || b2) = true -> P.
  Proof.
    Bool.destr_bool; auto.
  Qed.

  Lemma not_veq_false v w : S3.is_bfalse (S3.veq v w) = false -> v = null \/ w = null \/ v = w.
  Proof.
    destruct v; simpl.
    + destruct w; simpl.
      - destruct (c_eq b b0) eqn:eqc.
        * intros _. right. right. f_equal. apply Db.BaseConst_eqb_eq. exact eqc.
        * unfold S3.is_bfalse; simpl; intro Hfalse; discriminate Hfalse.
      - intros _. right. left. reflexivity.
    + intros _. left. reflexivity.
  Qed.

  Lemma S3_is_btrue_bneg : forall b, S3.is_btrue (S3.bneg b) = S3.is_bfalse b.
  Proof.
    intro. destr_tribool.
  Qed.

  Lemma S2_is_btrue_bneg : forall b, S2.is_btrue (S2.bneg b) = S2.is_bfalse b.
  Proof.
    intro. destruct b; auto.
  Qed.

  Lemma not_veq_false' v w : 
    S3.is_bfalse (S3.veq v w) = false <-> v = null \/ w = null \/ 
      exists cv cw, v = Some cv /\ w = Some cw /\ Db.c_eq cv cw = true.
  Proof.
    destruct v; simpl.
    + destruct w; simpl.
      - destruct (c_eq b b0) eqn:eqc.
        * split; intro.
          ++ right. right. exists b; exists b0. split. reflexivity. split. reflexivity. exact eqc.
          ++ reflexivity.
        * split.
          ++ unfold S3.is_bfalse; simpl; intro Hfalse; discriminate Hfalse.
          ++ intro. destruct H. discriminate H. destruct H. discriminate H.
             decompose record H. injection H0. injection H1. intros. subst. rewrite eqc in H3. discriminate H3.
      - split.
        * intros _. right. left. reflexivity.
        * intro. reflexivity.
    + split.
      * intros _. left. reflexivity.
      * intro. reflexivity.
  Qed.


End Facts.