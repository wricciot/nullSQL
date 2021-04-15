Require Import Eqdep Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool 
  Semantics JMeq FunctionalExtensionality Omega Coq.Init.Specif ProofIrrelevance EqdepFacts Util RelFacts SemFacts Common Eval.

Module Translation2V (Sql : SQL).
  Import Db.
  Import Sql.

  Module RF := RelFacts.Facts Sql.
  Module SF := SemFacts.Facts.
  Import RF.
  Import SF.

  Module S2 := Sem2.
  Module S3 := Sem3.
  Module Ev := Evl.
  Module SQLSem2 := SQLSemantics S2 Sql.
  Module SQLSem3 := SQLSemantics S3 Sql.

  (* just some trivial operations on names *)
  (* they will be moved to a separate module of names, which we may then assume *)
  Axiom freshlist : nat -> list Name.
  Axiom p_freshlist : forall n, List.NoDup (freshlist n).
  Axiom length_freshlist : forall n, length (freshlist n) = n.

  Definition cndeq : pretm -> pretm -> precond.
    refine (fun x y => cndpred 2 (fun l e => Db.c_eq (nth_lt l 0 _) (nth_lt l 1 _)) (x::y::List.nil)).
    + eapply (eq_rect_r _ _ e). Unshelve. repeat constructor.
    + eapply (eq_rect_r _ _ e). Unshelve. constructor.
  Defined.

  Fixpoint ttcond (d: Db.D) (c : precond) : precond :=
    match c with
    | cndmemb true tl Q => cndmemb true tl (ttquery d Q)
    | cndmemb false tl Q => 
        let al := freshlist (length tl) in
          cndnot (cndex (selstar false (((tbquery (ttquery d Q), al)::List.nil)::List.nil)
            (List.fold_right (fun (ta : pretm * Name) acc =>
              let (t,a) := ta in
              cndand (cndor (cndnull true (tmvar (0,a))) (cndor (cndnull true (tm_lift t 1)) (cndeq (tm_lift t 1) (tmvar (0,a))))) acc)
            cndtrue (List.combine tl al))))
    | cndex Q => cndex (ttquery d Q)
    | cndand c1 c2 => cndand (ttcond d c1) (ttcond d c2)
    | cndor c1 c2 => cndor (ttcond d c1) (ttcond d c2)
    | cndnot c1 => ffcond d c1
    | _ => c
    end
  with ffcond (d: Db.D) (c : precond) : precond :=
    match c with
    | cndtrue => cndfalse
    | cndfalse => cndtrue
    | cndnull b t => cndnull (negb b) t
    | cndpred n p tml => 
        cndand (cndnot c) 
          (List.fold_right (fun t acc => cndand (cndnull false t) acc) cndtrue tml)
    | cndmemb true tl Q => 
        let al := freshlist (length tl) in
          cndnot (cndex (selstar false (((tbquery (ttquery d Q), al)::List.nil)::List.nil)
            (List.fold_right (fun (ta : pretm * Name) acc =>
              let (t,a) := ta in
              cndand (cndor (cndnull true (tmvar (0,a))) (cndor (cndnull true (tm_lift t 1)) (cndeq (tm_lift t 1) (tmvar (0,a))))) acc)
            cndtrue (List.combine tl al))))
    | cndmemb false tl Q => cndmemb true tl (ttquery d Q)
    | cndex Q => cndnot (cndex (ttquery d Q))
    | cndand c1 c2 => cndor (ffcond d c1) (ffcond d c2)
    | cndor c1 c2 => cndand (ffcond d c1) (ffcond d c2)
    | cndnot c1 => ttcond d c1
    end
  with ttquery (d: Db.D) (Q : prequery) : prequery :=
    match Q with
    | select b btm btbl c => 
        select b btm (List.map (fun btb => 
          List.map (fun bt => (tttable d (fst bt), snd bt)) btb) btbl) 
        (ttcond d c)
    | selstar b btbl c => 
        selstar b (List.map (fun btb => 
          List.map (fun bt => (tttable d (fst bt), snd bt)) btb) btbl)
        (ttcond d c)
    | qunion b Q1 Q2 => qunion b (ttquery d Q1) (ttquery d Q2)
    | qinters b Q1 Q2 => qinters b (ttquery d Q1) (ttquery d Q2)
    | qexcept b Q1 Q2 => qexcept b (ttquery d Q1) (ttquery d Q2)
    end
  with tttable (d: Db.D) (T : pretb) : pretb :=
    match T with
    | tbquery Q => tbquery (ttquery d Q)
    | _ => T
    end
  .

  Lemma j_select_inv :
    forall d g b btm btbl c s, forall P : (forall g0 q0 s0, j_query d g0 q0 s0 -> Prop),
    (forall g1 H, forall Hbtbl : j_btbl d g btbl g1, forall Hc : j_cond d (g1 ++ g) c,
     forall Html : j_tml (g1 ++ g) (List.map fst btm), forall Hs : s = List.map snd btm,
       H = j_select _ _ _ _ _ _ _ _ Hbtbl Hc Html Hs -> P g (select b btm btbl c) s H) ->
    forall H : j_query d g (select b btm btbl c) s,
    P g (select b btm btbl c) s H.
  intros d g b btm btbl c s P Hinv H. dependent inversion H.
  eapply Hinv. trivial.
  Qed.

  Theorem j_query_j_db : forall d G Q s, j_query d G Q s -> j_db d.
  intros d G Q s HWF.
  eapply (jq_ind_mut _ 
          (fun G0 Q0 s0 H0 => j_db d)
          (fun G0 T0 s0 H0 => j_db d)
          (fun G0 c0 H0 => j_db d)
          (fun G0 btbl G1 H0 => j_db d) 
          (fun G0 btb G1 H0 => j_db d) 
          (fun G0 Q0 H0 => j_db d)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF).
  Unshelve. all: simpl; intros; auto.
  Qed.

  Lemma aux_j_var_findpos' a s :
    j_var a s -> 
    forall m, exists n, n < m + length s /\ findpos s (fun x => if Db.Name_dec x a then true else false) m = Some n.
  Proof.
    intro H. elim H; simpl.
    + intros. exists m. destruct (Db.Name_dec a a); intuition.
    + intros. destruct (Db.Name_dec b a); intuition.
      - rewrite e in H0. contradiction H0. reflexivity.
      - destruct (H2 (S m)). destruct H3.
        exists x. split; auto; omega.
  Qed.

  Lemma j_var_findpos' a s (Ha : j_var a s) : findpos s (fun x => if Db.Name_dec x a then true else false) 0 <> None.
  Proof.
    destruct (aux_j_var_findpos' _ _ Ha 0). destruct H. rewrite H0. intro Hfalse. discriminate Hfalse.
  Qed.

  Definition Fin_findpos a s (Ha : j_var a s) : Fin.t (length s).
    refine (@Fin.of_nat_lt (unopt (findpos s (fun x => if Db.Name_dec x a then true else false) 0) _) _ _).
    Unshelve. Focus 2. apply j_var_findpos'. exact Ha.
    destruct (aux_j_var_findpos' _ _ Ha 0). destruct H.
    generalize (j_var_findpos' a s Ha). rewrite H0. intros. simpl. exact H.
  Defined.

  Lemma findpos_m_Some_step A (s : list A) p :
      forall m n, findpos s p m = Some n -> findpos s p (S m) = Some (S n).
  Proof.
    elim s.
    + simpl. intros. discriminate H.
    + simpl. intros. destruct (p a).
      - injection H0. intuition.
      - apply H. exact H0.
  Qed.

  Lemma findpos_m_Some A (s : list A) p m :
      forall n, findpos s p 0 = Some n -> findpos s p m = Some (m + n).
  Proof.
    elim m.
    + simpl. intuition.
    + simpl. intros. apply findpos_m_Some_step. apply H. exact H0.
  Qed.

  Lemma findpos_tech a s : forall s1 s2, s = s1 ++ a :: s2 -> ~ List.In a s1 ->
    forall m, findpos s (fun x => if Db.Name_dec x a then true else false) m = Some (m + length s1).
  Proof.
    intros s1 s2 Hs. rewrite Hs. elim s1; simpl; intros.
    + destruct (Db.Name_dec a a). f_equal. omega. contradiction n. reflexivity.
    + destruct (Db.Name_dec a0 a). contradiction H0. left. exact e.
      rewrite H. f_equal. omega. intro. contradiction H0. right. exact H1.
  Qed.

  Lemma j_var_notin s1 s2 a : j_var a (s1 ++ a :: s2) -> ~ List.In a s1.
  Proof.
    elim s1; simpl; intros; intuition.
    + inversion H0. contradiction H3. apply in_or_app. right. left. reflexivity.
      contradiction H4. symmetry. exact H2.
    + inversion H0. contradiction H3. apply in_or_app. right. left. reflexivity.
      apply H; assumption.
  Qed.

  Lemma Fin_findpos_tech a s Ha : forall s1 s2, s = s1 ++ a :: s2 -> 
    proj1_sig (Fin.to_nat (Fin_findpos a s Ha)) = length s1.
  Proof.
    intros. enough (exists H1 H2, Fin_findpos a s Ha = @Fin.of_nat_lt (unopt (findpos s (fun x => if Db.Name_dec x a then true else false) 0) H1) _ H2).
    erewrite findpos_tech in H0. Focus 2. exact H.
    decompose record H0. rewrite H2.
    rewrite Fin.to_nat_of_nat. simpl. reflexivity.
    clear H0. rewrite H in Ha. apply (j_var_notin _ _ _ Ha).
    eexists. eexists. reflexivity.
  Qed.

  Lemma in_nodup_j_var a s : List.In a s -> List.NoDup s -> j_var a s.
  Proof.
    elim s.
    + simpl. intuition.
    + intros b s' IH Hin Hnodup. cut (count_occ Db.Name_dec (b :: s') a > 0).
      - simpl. destruct (Db.Name_dec b a).
        * intros _. rewrite e. constructor. inversion Hnodup. rewrite e in H1. exact H1.
        * intro Hcount. constructor 2; auto. apply IH.
          ++ inversion Hin; auto. contradiction n.
          ++ inversion Hnodup. exact H2.
      - apply count_occ_In. exact Hin.
  Qed.

  Lemma tech_j_cond_fold_vect d s0 n (s : Vector.t Name n) g (tml : Vector.t pretm n) :
    List.NoDup s0 -> j_db d -> j_tml g (to_list tml) -> incl (to_list s) s0 ->
    j_cond d ((s0 :: Datatypes.nil) ++ g) (List.fold_right
     (fun (ta : pretm * Name) (acc : precond) => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc)
     (TRUE) (combine (to_list tml) (to_list s))).
  Proof.
    intros Hnodup Hdb.
    eapply (Vector.rect2 (fun n s' tml' => 
      j_tml g (to_list tml') -> incl (to_list s') s0 -> 
      j_cond d ((s0 :: List.nil) ++ g) (List.fold_right
        (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
        (combine (to_list tml') (to_list s'))))
      _ _ s tml). Unshelve.
    + simpl. intros. constructor. exact Hdb.
    + simpl. intros m s' tml' IH a0 t0 Html' Hincl. constructor.
      - constructor.
        * constructor; auto. econstructor. reflexivity. apply in_nodup_j_var; auto. apply Hincl. left. reflexivity.
        * constructor.
          ++ constructor; auto. unfold j_tml in Html'. eapply (j_tm_weak _ (s0::List.nil)). apply Html'. left. reflexivity.
          ++ constructor; auto. intro. intro Ht.
            destruct (pretm_dec t (tm_lift t0 1)).
            -- rewrite e. eapply (j_tm_weak _ (s0::List.nil)). apply Html'. left. reflexivity.
            -- destruct (pretm_dec t (tmvar (0, a0))).
              ** rewrite e. eapply j_tmvar. reflexivity. apply in_nodup_j_var.
                +++ apply Hincl. left. reflexivity.
                +++ refine (let IH' := IH _ _ in _). Unshelve.
                  --- clearbody IH'. apply Hnodup.
                  --- intro. intro. apply Html'. right. exact H.
                  --- intro. intro. apply Hincl. right. exact H.
              ** destruct Ht. contradiction n0. symmetry. exact H.
                 destruct H. contradiction n1. symmetry. exact H.
                 contradiction H.
      - apply IH.
        * unfold j_tml. intros t1 Ht1. apply Html'. right. exact Ht1.
        * unfold incl. intros a1 Ha1. apply Hincl. right. exact Ha1.
  Qed.

  Lemma tech_j_cond_fold d s0 s g tml :
    length tml = length s -> List.NoDup s0 -> j_db d -> j_tml g tml -> incl s s0 ->
    j_cond d ((s0 :: Datatypes.nil) ++ g) (List.fold_right
     (fun (ta : pretm * Name) (acc : precond) => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc)
     (TRUE) (combine tml s)).
  Proof.
    intro Hlen. rewrite <- (to_list_of_list_opp tml). rewrite <- (to_list_of_list_opp s).
    generalize (of_list tml) (of_list s). rewrite Hlen. intros vtml vs. apply tech_j_cond_fold_vect.
  Qed.

  Lemma sem3_pred_ttrue' : forall n p vl e,
    S3.sem_bpred n p vl e = ttrue ->
    exists (cl : list BaseConst) (Hcl : length cl = n),
      monadic_map (fun val : option BaseConst => val) vl = Some cl /\ p cl Hcl = true.
  Proof.
    intros n p vl e.
    apply S3.sem_bpred_elim.
    - intros cl e0 Hcl Hp. exists cl. exists Hcl. split. rewrite e0. reflexivity.
      destruct (p cl Hcl) eqn:e1; auto; simpl in Hp; discriminate Hp.
    - intros _ Hfalse. discriminate Hfalse.
  Qed.

  Lemma sem3_pred_tfalse' : forall n p vl e,
    S3.sem_bpred n p vl e = tfalse ->
    exists (cl : list BaseConst) (Hcl : length cl = n),
      monadic_map (fun val : option BaseConst => val) vl = Some cl /\ p cl Hcl = false.
  Proof.
    intros n p vl e.
    apply S3.sem_bpred_elim.
    - intros cl e0 Hcl Hp. exists cl. exists Hcl. split. rewrite e0. reflexivity.
      destruct (p cl Hcl) eqn:e1; auto; simpl in Hp; discriminate Hp.
    - intros _ Hfalse. discriminate Hfalse.
  Qed.

  Lemma sem3_pred_unknown' : forall n p vl e,
    S3.sem_bpred n p vl e = unknown ->
      monadic_map (fun val : option BaseConst => val) vl = @None (list BaseConst).
  Proof.
    intros n p vl e.
    apply S3.sem_bpred_elim.
    + intros cl e0 Hcl. destruct (p cl Hcl); simpl; intro Hfalse; discriminate Hfalse.
    + intros H _. exact H.
  Qed.

  Lemma sem2_pred_true_aux' (d : D) (g : Ctx) tml Stml x h:
    SQLSem2.j_tml_sem g tml Stml ->
    monadic_map (fun val => val) (to_list (Stml h)) = Some x ->
    forall Sc, SQLSem2.j_cond_sem d g (List.fold_right (fun (t : pretm) (acc : precond) => 
      (t IS NOT NULL) AND acc) (TRUE) tml) Sc ->
    Sc h = true.
  Proof.
    intros Html Hmap.
    enough (forall t0 St0, List.In t0 tml -> SQLSem2.j_tm_sem g t0 St0 -> exists v, St0 h = Some v).
    + generalize H. clear H Hmap Html. elim tml; simpl; intros.
      - inversion H0. apply (existT_eq_elim H2). intros. rewrite <- H4. reflexivity.
      - inversion H1. apply (existT_eq_elim H5). intros. rewrite <- H9. clear H5 H8 H9.
        apply S2_is_btrue_and_intro.
        ++ inversion H6. apply (existT_eq_elim H11). intros. rewrite <- H13. clear H11 H12 H13.
           destruct (H0 _ _ (or_introl eq_refl) H9). rewrite H11. reflexivity.
        ++ apply H. intros. apply (H0 _ _ (or_intror H5) H8). exact H7.
    + generalize x Hmap; clear x Hmap. induction Html; simpl; intros.
      - contradiction H.
      - destruct H0.
        * generalize dependent Hmap. apply bind_elim. Focus 2. intros. discriminate Hmap.
          intros cl Hmap. apply bind_elim. Focus 2. intros. discriminate Hmap0.
          intros c Hc Hinj. unfold ret in Hinj. injection Hinj. clear Hinj. intro Hinj. exists c.
          rewrite <- Hc. rewrite H0 in H. rewrite (SQLSem2.j_tm_sem_fun _ _ _ H _ H1). reflexivity.
        * generalize dependent Hmap. apply bind_elim. Focus 2. intros. discriminate Hmap. 
          intros cl Hmap. intros. apply (IHHtml _ Hmap _ _ H0 H1).
  Qed.

  Lemma sem2_pred_false_aux' (d : D) (g : Ctx) tml Stml h :
    SQLSem2.j_tml_sem g tml Stml ->
    monadic_map (fun val => val) (to_list (Stml h)) = @None (list BaseConst) ->
    forall Sc, SQLSem2.j_cond_sem d g (List.fold_right (fun (t : pretm) (acc : precond) => 
      (t IS NOT NULL) AND acc) (TRUE) tml) Sc ->
    Sc h = false.
  Proof.
    intros Html Hmap.
    cut (forall h t0 tml0 St0, SQLSem2.j_tm_sem g t0 St0 -> St0 h = None -> List.In t0 tml0 -> 
      forall Sc0, SQLSem2.j_cond_sem d g (List.fold_right (fun t1 acc => 
      (t1 IS NOT NULL) AND acc) (TRUE) tml0) Sc0 -> Sc0 h = false).
    + intro Hcut. cut (exists t, List.In t tml /\ exists St, SQLSem2.j_tm_sem g t St /\ St h = None).
      - intros H Sc Hc. decompose record H. apply (Hcut _ _ _ _ H2 H3 H1 Sc Hc).
      - generalize dependent Hmap. generalize dependent Stml. clear Hcut. elim tml.
        * intros Stml Html Hfalse. inversion Html. apply (existT_eq_elim H0); intros. rewrite <- H1 in Hfalse.
          simpl in Hfalse. discriminate Hfalse.
        * intros hd tl IH Stml Html. inversion Html. apply (existT_eq_elim H2); intros. rewrite <- H5 in Hmap. 
          generalize dependent Hmap. simpl. apply bind_elim; simpl. 
          intros cl Hcl. apply bind_elim. intros c Hc Hfalse. discriminate Hfalse.
          intros Ht _. exists hd. split. intuition. exists St. intuition.
          intros Hmap _. destruct (IH _ H3 Hmap). destruct H6. destruct H7.
          exists x. split. right. exact H6. exists x0. exact H7.
    + intros h0 t0 tml0. generalize dependent t0. elim tml0.
      - simpl. intros. contradiction H1.
      - simpl. intros t1 tml1 IH t0 St0 Ht0 Hnone Hin Sc0 Hc0. inversion Hc0.
        apply (existT_eq_elim H2); intros. rewrite <- H6. destruct Hin.
        * subst. inversion H3. apply (existT_eq_elim H7); intros. rewrite <- H9.
          rewrite (SQLSem2.j_tm_sem_fun _ _ _ H1 _ Ht0). rewrite Hnone. reflexivity.
        * rewrite (IH _ _ Ht0 Hnone H7 _ H4). apply Bool.andb_false_intro2. reflexivity.
  Qed.

(* XXX: Why SQLSem2.j_tml_sem and not 3VL? *)
  Lemma sem_bpred_tech : forall d G tml Stml h n p e,
    SQLSem2.j_tml_sem G tml Stml ->
    forall Sc, SQLSem2.j_cond_sem d G (List.fold_right (fun t acc => cndand (cndnull false t) acc) cndtrue tml) Sc
      -> S3.is_btrue (negtb (S3.sem_bpred n p (to_list (Stml h)) e)) 
         = S2.is_btrue (S2.band (S2.bneg (S2.sem_bpred n p (to_list (Stml h)) e)) (Sc h)).
  Proof.
    intros. destruct (S3.sem_bpred n p (to_list (Stml h)) e) eqn:e0.
    * destruct (sem3_pred_ttrue' _ _ _ _ e0). destruct H1.
      simpl. symmetry. apply S2.sem_bpred_elim.
      ++ intros. apply S2_is_btrue_false_and1. destruct H1.
         rewrite H1 in H2. replace (p cl Hcl) with (p x x0). rewrite H3. reflexivity.
         injection H2. intro. generalize Hcl. clear Hcl. rewrite <- H4. intro.
         f_equal. apply EqdepTheory.UIP.
      ++ destruct H1. rewrite H1. intro Hfalse. discriminate Hfalse.
    * destruct (sem3_pred_tfalse' _ _ _ _ e0).
      simpl. symmetry. destruct H1. destruct H1. apply S2_is_btrue_and_intro.
      ++ apply S2.sem_bpred_elim.
         -- rewrite H1. intros. injection H3. intro. generalize Hcl; clear Hcl. rewrite <- H4. intro.
            replace (p x Hcl) with (p x x0). rewrite H2. reflexivity.
            f_equal. apply EqdepTheory.UIP.
         -- rewrite H1. intro Hfalse. discriminate Hfalse.
      ++ replace (Sc h) with true. reflexivity. symmetry. apply (sem2_pred_true_aux' _ _ _ _ _ _ H H1 _ H0).
    * simpl. symmetry. apply S2_is_btrue_false_and2.
      erewrite (sem2_pred_false_aux' _ _ _ _ _ H _ _ H0). Unshelve. reflexivity.
      apply (sem3_pred_unknown' _ _ _ _ e0).
  Qed.

(* XXX: same as above *)
  Lemma fold_v_tml_sem1' g m tml Stml (Html : SQLSem2.j_tml_sem g tml Stml) h Vl :
          Vl ~= Stml h ->
           (fun rl => fold_right2 (fun r0 V0 acc => 
              acc && S2.is_btrue (S2.veq r0 V0))%bool true m rl Vl)
           = (fun rl => fold_right2 (fun r0 V0 acc => 
              acc && S3.is_btrue (S3.veq r0 V0))%bool true m rl Vl).
  Proof.
    intro HVl. extensionality rl.
    eapply (Vector.rect2 (fun n rl0 tml0 => 
      (fold_right2 (fun (r0 V0 : option BaseConst) (acc : bool) => (acc && S2.is_btrue (S2.veq r0 V0))%bool) true n rl0 tml0 =
       fold_right2 (fun (r0 V0 : option BaseConst) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true n rl0 tml0)) 
      _ _ rl Vl). Unshelve.
    + reflexivity.
    + intros n v1 v2 IH x1 x2. simpl. f_equal.
      - apply IH.
      - unfold S2.veq, S3.veq. destruct x1, x2; try reflexivity. destruct (c_eq b b0); reflexivity.
  Qed.

  Definition is_subenv' {n} (ul : Rel.T n) {m} {s} {g} (Hlen : length s = m + n) (h : Ev.env (s::g)) := 
    forall a (Ha: j_var a s) k (Hk : k < n), proj1_sig (Fin.to_nat (Fin_findpos a s Ha)) = k + m ->
    exists Sa, Ev.j_var_sem s a Sa /\ Sa (@Ev.subenv1 (s::List.nil) g h) = nth ul (Fin.of_nat_lt Hk).

  Lemma cons_is_subenv' t {n} (ul : Rel.T n) {s} {g} (h : Ev.env (s::g)) :
    forall m m' (H1 : length s = m + S n) (H2 : length s = m' + n), 
    is_subenv' (cons _ t _ ul) H1 h -> is_subenv' ul H2 h.
  Proof.
    unfold is_subenv'. intros. cut (S k < S n).
    + intro HSk. replace (nth ul (Fin.of_nat_lt Hk)) with (nth (cons _ t _ ul) (Fin.of_nat_lt HSk)).
      - apply (H _ Ha). rewrite H0. omega.
      - simpl. f_equal. apply Fin.of_nat_ext.
    + omega.
  Qed.

  Lemma cond_sem_cndeq_true1' d G t1 t2 St1 St2 h k :
    SQLSem2.j_tm_sem G t1 St1 -> SQLSem2.j_tm_sem G t2 St2 ->
    St1 h = Some k -> St2 h = Some k ->
    exists Sc, SQLSem2.j_cond_sem d G (cndeq t1 t2) Sc /\ Sc h = true.
  Proof.
    intros Ht1 Ht2 eSt1 eSt2. eexists. 
    unfold cndeq. split.
    + econstructor. econstructor. exact Ht1. econstructor. exact Ht2. econstructor.
    + hnf. 
      cut (forall p0 e0, p0 = (fun l (e : length l = 2) =>
          c_eq (nth_lt l 0 (eq_rect_r (lt 0) (le_S 1 1 (le_n 1)) e))
            (nth_lt l 1 (eq_rect_r (lt 1) (le_n 2) e))) ->
          S2.sem_bpred 2 p0 (St1 h::St2 h::List.nil) e0 = true).
      intro Hcut. apply Hcut. reflexivity.
      intros. apply S2.sem_bpred_elim.
      - intro. rewrite eSt1, eSt2. simpl. intro Hret. injection Hret. clear Hret. intros Hret.
        rewrite <- Hret. simpl. intro Htriv.
        rewrite (UIP_refl _ _ Htriv). rewrite H. repeat rewrite eq_rect_r_eq_refl. 
        unfold S2.of_bool, nth_lt. simpl. apply Db.BaseConst_eqb_eq. reflexivity.
      - simpl. rewrite eSt1, eSt2. simpl. intro Hfalse. discriminate Hfalse. 
        Unshelve. reflexivity.
  Qed.

  Lemma cond_sem_cndeq_true2' d G t1 t2 Sc St1 St2 h :
    SQLSem2.j_cond_sem d G (cndeq t1 t2) Sc -> Sc h = true -> 
    SQLSem2.j_tm_sem G t1 St1 -> SQLSem2.j_tm_sem G t2 St2 ->
    exists k, St1 h = Some k /\ St2 h = Some k.
  Proof.
    intros Hc eSc Ht1 Ht2. inversion Hc. 
    apply (existT_eq_elim H2); intros; subst; clear H2.
    apply (existT_eq_elim H4); intros; subst; clear H4.
    clear H H5.
    eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => _) _ H1). Unshelve. intros.
    apply (existT_eq_elim H5); intros; subst; clear H5 H6.
    eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => _) _ H4). Unshelve. intros.
    apply (existT_eq_elim H8); intros; subst; clear H8 H9.
    inversion H5. apply (existT_eq_elim H7); intros; subst; clear H7 H6.
    generalize dependent eSc. apply S2.sem_bpred_elim.
    + unfold to_list. replace St with St1. replace St0 with St2.
      destruct (St1 h) eqn:Hk1.
      - destruct (St2 h) eqn:Hk2.
        * simpl. intros cl ecl. injection ecl. clear ecl. intro ecl. rewrite <- ecl.
          intro Hcl. rewrite (UIP_refl _ _ Hcl). simpl. repeat rewrite eq_rect_r_eq_refl.
          unfold S2.of_bool, nth_lt. simpl. intro Heq. enough (b0 = b).
          -- rewrite H6. exists b. intuition.
          -- symmetry. apply Db.BaseConst_eqb_eq. exact Heq.
        * intros cl Hfalse. discriminate Hfalse.
      - destruct (St2 h); intros cl Hfalse; discriminate Hfalse.
      - apply (SQLSem2.j_tm_sem_fun _ _ _ Ht2 _ H3).
      - apply (SQLSem2.j_tm_sem_fun _ _ _ Ht1 _ H2).
    + intros _ Hfalse. discriminate Hfalse.
  Qed.

  (* XXX: SQLSem2/3? *)
  Lemma cond_sem_not_neq_iff' d g s tml (Hlen : length s = length tml) : 
    forall Stml Sc (ul : Rel.T (length tml)), 
    forall h h' h'', h = Ev.env_app (s::List.nil) _ h'' h' -> is_subenv' ul (Hlen : length s = 0 + length tml) h ->
    SQLSem2.j_cond_sem d (s :: g)%list 
      (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in 
        (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
        (TRUE) (combine tml s))
      Sc ->
    SQLSem2.j_tml_sem g tml Stml -> 
    (Sc h = true <-> forall i, S3.is_bfalse (S3.veq (nth ul i) (nth (Stml h') i)) = false).
  Proof.
    eapply (@list_rect2 _ _ (fun s0 tml0 =>
      forall s1, s = s1 ++ s0 ->
      forall (Hlen0: length s = length s1 + length tml0),
      forall Stml Sc (ul: Rel.T (length tml0)) h h' h'', 
      h = Ev.env_app (s::List.nil) _ h'' h' -> 
      is_subenv' ul Hlen0 h ->
      SQLSem2.j_cond_sem d (s :: g)
        (List.fold_right (fun (ta : pretm * Name) acc =>
          let (t,a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml0 s0)) Sc -> 
      SQLSem2.j_tml_sem g tml0 Stml ->
      Sc h  = true
      <-> (forall i, S3.is_bfalse (S3.veq (nth ul i) (nth (Stml h') i)) = false))
      _ _ _ _  Hlen List.nil eq_refl Hlen). Unshelve.
    + simpl. intros. split; intro.
      - intro. inversion i.
      - generalize h. inversion H2. intros. apply (existT_eq_elim H6). intros; subst. reflexivity.
    + simpl. intros x t s0 tml0 Hlen0 IH s1 Hs Hlens Stml0 Sc ul h h' h'' Happ Hsub Hc Html. split; intro.
      - intro i.
        cut (forall St, SQLSem2.j_tm_sem g t St -> nth ul Fin.F1 = null \/ St h' = Db.null \/ St h' = nth ul Fin.F1).
        * generalize dependent Hsub.
          cut (forall i0 (ul1 : Rel.T (S (length tml0))), i0 ~= i -> ul1 ~= ul -> 
            is_subenv' ul1 Hlens h ->
            (forall St, SQLSem2.j_tm_sem g t St -> nth ul1 Fin.F1 = null \/ St h' = null \/ St h' = nth ul1 Fin.F1) ->
            S3.is_bfalse (S3.veq (nth ul i0) (nth (Stml0 h') i)) = false). intro Hcut. apply Hcut. reflexivity. reflexivity.
          dependent inversion ul with (fun m (ul0 : Rel.T m) => forall i0 (ul1 : Rel.T (S (length tml0))),
            i0 ~= i -> ul1 ~= ul0 -> is_subenv' ul1 Hlens h ->
            (forall St, SQLSem2.j_tm_sem g t St -> nth ul1 Fin.F1 = null \/ St h' = null \/ St h' = nth ul1 Fin.F1) ->
            S3.is_bfalse (S3.veq (nth ul0 i0) (nth (Stml0 h') i)) = false).
          intros i0 ul1 Hi0 Hul1; rewrite Hi0, Hul1; clear Hi0. intro Hsub.
          cut (exists St Stml1, SQLSem2.j_tm_sem g t St /\ SQLSem2.j_tml_sem g tml0 Stml1).
          ++ intro. decompose record H0. clear H0.
             replace (Stml0 h') with (Vector.cons _ (x0 h') _ (x1 h')).
             intro Hcut. simpl in Hcut.
            cut (forall (ul0 vl0 : Rel.T (S (length tml0))), 
              ul0 ~= cons _ h0 _ t0 ->
              vl0 ~= cons _ (x0 h') _ (x1 h') ->
              S3.is_bfalse (S3.veq (nth ul0 i) (nth vl0 i)) = false).
            -- intro Hcut1. apply Hcut1; reflexivity.
            -- dependent inversion i with (fun (n1 : nat) (i0 : Fin.t n1) => 
                forall ul0 vl0, ul0 ~= cons _ h0 (length tml0) t0 -> 
                vl0 ~= cons _ (x0 h') _ (x1 h') ->
                S3.is_bfalse (S3.veq (nth ul0 i0) (nth vl0 i0)) = false);
                intros ul0 vl0 Hul0 Hvl0; rewrite Hul0, Hvl0; clear Hul0 Hvl0.
              ** simpl. destruct (Hcut x0 H2).
                +++ rewrite H0; simpl; reflexivity. 
                +++ destruct H0.
                  --- rewrite H0. unfold S3.veq. destruct h0; simpl; reflexivity.
                  --- rewrite H0. destruct h0; simpl; try reflexivity.
                      replace (c_eq b b) with true; auto.
                      symmetry. apply Db.BaseConst_eqb_eq. reflexivity.
              ** simpl. generalize H. 
                cut (forall h0, h0 ~= h -> Sc h0 = true -> S3.is_bfalse (S3.veq (nth t0 t1) (nth (x1 h') t1)) = false).
                intro Hcut1. apply Hcut1. reflexivity.
                inversion Hc. intros h1 Hh1; rewrite Hh1; clear h1 Hh1.
                apply (existT_eq_elim H7); intros; subst.
                eapply (S2_is_btrue_and_elim _ _ _ _ H12). Unshelve. intros Hc1 Hc2.
                cut (length (s1 ++ x :: s0) = length (s1 ++ (x::List.nil)) + length tml0).
                +++ intro Hcut1. eapply (IH _ _ Hcut1 x1 _ _ _ h' h'' eq_refl _ H9 H4). Unshelve.
                  --- exact Hc2. 
                  --- rewrite <- app_assoc. reflexivity.
                  --- eapply cons_is_subenv'. exact Hsub.
                +++ do 2 rewrite app_length. simpl. rewrite Hlen0. omega.
            -- apply JMeq_eq. assert (forall h1, h1 ~= h' -> cons _ (x0 h') _ (x1 h') ~= Stml0 h1).
                eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => forall h1, h1 ~= h' ->
                        cons _ (x0 h') _ (x1 h') ~= S' h1) _ Html). Unshelve. Focus 2.
               simpl. intros. apply (existT_eq_elim H8); intros; subst; clear H8. apply eq_JMeq.
               f_equal. rewrite (SQLSem2.j_tm_sem_fun _ _ _ H2 _ H3). reflexivity.
               rewrite (SQLSem2.j_tml_sem_fun _ _ _ H4 _ H5). reflexivity.
               apply H0. reflexivity.
          ++ eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => 
                exists St Stml1, SQLSem2.j_tm_sem g t St /\ SQLSem2.j_tml_sem g tml0 Stml1) _ Html). Unshelve.
             simpl. intros. apply (existT_eq_elim H6); intros; subst; clear H6. exists St. exists Stml1.
             split. exact H2. exact H4.
        * generalize Hc, H. cut (forall h0, h0 ~= h -> SQLSem2.j_cond_sem d (s :: g)
            (((tmvar (0, x) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))))
              AND List.fold_right (fun (ta : pretm * Name) (acc : precond) => let (t0, a) := ta in
              ((tmvar (0, a) IS NULL) OR ((tm_lift t0 1 IS NULL) OR cndeq (tm_lift t0 1) (tmvar (0, a)))) AND acc)
             (TRUE) (combine tml0 s0)) Sc -> Sc h0 = true ->
            forall St, SQLSem2.j_tm_sem g t St -> nth ul Fin.F1 = null \/ St h' = null \/ St h' = nth ul Fin.F1).
            intro Hcut1; apply Hcut1; reflexivity.
          inversion Hc. intros h1 Hh1; rewrite Hh1; clear h1 Hh1.
          apply (existT_eq_elim H3); intros; subst.
          eapply (S2_is_btrue_and_elim _ _ _ _ H9). Unshelve. intros Hc1 _.
          generalize Hc1; clear Hc1.
          cut (forall h0, h0 ~= Ev.env_app _ _ h'' h' -> S2.is_btrue
                (Sc1 h0) = true ->
                (* forall Ht : j_tm g t, *) nth ul Fin.F1 = null \/ St h' = null \/ St h' = nth ul Fin.F1).
            intro Hcut1; apply Hcut1; reflexivity.
          inversion H4. apply (existT_eq_elim H7). intros _ HSc1 h0 Hh0 Hc1. subst.
          inversion H12. apply (existT_eq_elim H13); intros; subst.
          eapply (S2_is_btrue_or_elim _ _ _ _ _ Hc1). Unshelve.
          ++ left.
             inversion H11. apply (existT_eq_elim H19); intros; subst; clear H19.
             destruct (St0 (Ev.env_app _ _ h'' h')) eqn:Hsem. discriminate H0. 
             inversion H17. inversion H19. apply (existT_eq_elim H22); intros; subst; clear H22.
             assert (Hsuba : j_var x (s1 ++ x :: s0)). apply (SQLSem2.j_var_sem_j_var _ _ _ H25).
             assert (Hsubk : 0 < S (length tml0)). omega.
             assert (Hfind : proj1_sig (Fin.to_nat (Fin_findpos x (s1 ++ x :: s0) Hsuba)) = 0 + length s1).
             rewrite (Fin_findpos_tech _ _ _ _ _ eq_refl). reflexivity.
             destruct (Hsub _ Hsuba _ Hsubk Hfind). destruct H1.
             replace (nth ul Fin.F1) with (nth ul (Fin.of_nat_lt Hsubk)). rewrite <- H2.
             rewrite (Ev.j_var_sem_fun _ _ _ H1 _ H25). unfold null. rewrite <- Hsem. reflexivity.
             reflexivity.
          ++ intro. eapply (S2_is_btrue_or_elim _ _ _ _ _ H0). Unshelve.
            -- intro. inversion H14. apply (existT_eq_elim H20); intros; subst; clear H20.
               pose (H10' := SQLSem2.j_tm_sem_weak _ ((s1++x::s0)::List.nil) _ _ H10); clearbody H10'.
               rewrite (SQLSem2.j_tm_sem_fun _ _ _ H18 _ H10') in H1. 
               replace (St (Ev.subenv2 (Ev.env_app ((s1 ++ x :: s0) :: Datatypes.nil) g h'' h'))) with (St h') in H1.
               destruct (St h'); try discriminate H1. right. left. reflexivity.
               f_equal. apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
               transitivity (skipn (length (projT1 h'')) (projT1 h'' ++ projT1 h')).
               rewrite Ev.skipn_append. reflexivity. f_equal. rewrite Ev.length_env. reflexivity.
            -- intro. right. right.
               inversion H14. apply (existT_eq_elim H20); intros; subst; clear H20.
               inversion H11. apply (existT_eq_elim H22); intros; subst; clear H22.
               enough (exists k, St0 (Ev.env_app _ _ h'' h') = Some k /\ St1 (Ev.env_app _ _ h'' h') = Some k).
               decompose record H2.
               inversion H19. inversion H26. apply (existT_eq_elim H28); intros; subst; clear H28.
               assert (Hsuba : j_var x (s1 ++ x :: s0)). apply (SQLSem2.j_var_sem_j_var _ _ _ H31). 
               assert (Hsubk : 0 < S (length tml0)). omega.
               assert (Hfind : proj1_sig (Fin.to_nat (Fin_findpos x (s1 ++ x :: s0) Hsuba)) = 0 + length s1).
               rewrite (Fin_findpos_tech _ _ _ _ _ eq_refl). reflexivity.
               destruct (Hsub _ Hsuba _ Hsubk Hfind). destruct H17.
               replace (nth ul Fin.F1) with (nth ul (Fin.of_nat_lt Hsubk)). rewrite <- H24.
               rewrite (Ev.j_var_sem_fun _ _ _ H17 _ H31).
               unfold Scm in H22. rewrite H22. rewrite <- H20.
               pose (H10' := SQLSem2.j_tm_sem_weak _ ((s1++x::s0)::List.nil) _ _ H10); clearbody H10'.
               rewrite (SQLSem2.j_tm_sem_fun _ _ _ H18 _ H10'). f_equal. apply Ev.env_eq. 
               unfold Ev.subenv2, Ev.env_app. simpl.
               transitivity (skipn (length (projT1 h'')) (projT1 h'' ++ projT1 h')).
               rewrite Ev.skipn_append. reflexivity. f_equal. rewrite Ev.length_env. reflexivity.
               reflexivity. eapply cond_sem_cndeq_true2'; eauto.
      - inversion Hc. apply (existT_eq_elim H3); intros; subst; clear H3.
        inversion H4. apply (existT_eq_elim H3); intros; subst; clear H3.
        inversion H8. apply (existT_eq_elim H3); intros; subst; clear H3.
        apply S2_is_btrue_and_intro.
        * destruct (Sc0 (Ev.env_app _ _ h'' h')) eqn:eSc0; auto.
          inversion H7. apply (existT_eq_elim H13); intros; subst; clear H13.
          destruct (St (Ev.env_app _ _ h'' h')) eqn:eSt.
          ++ inversion H10. apply (existT_eq_elim H15); intros; subst; clear H15.
             cut (St0 (Ev.env_app _ _ h'' h') = null \/
                  St0 (Ev.env_app _ _ h'' h') = St (Ev.env_app _ _ h'' h')).
            -- intro Hcut; destruct Hcut.
              ** rewrite H0; simpl. reflexivity.
              ** rewrite H0, eSt. simpl. 
                 destruct (cond_sem_cndeq_true1' d _ _ _ _ _ (Ev.env_app _ _ h'' h') b H3 H2).
                 rewrite H0. exact eSt. exact eSt. decompose record H1; clear H1.
                 rewrite <- H15.
                 erewrite (SQLSem2.jc_sem_fun_dep _ _ _ _ H11 _ _ _ _ _ H13). reflexivity.
                 Unshelve. reflexivity. reflexivity.
            -- cut (exists St0', SQLSem2.j_tm_sem g t St0').
               ** intro Ht0'. destruct Ht0'. replace (St0 (Ev.env_app _ _ h'' h')) with (x0 h').
                  inversion H2. inversion H17. apply (existT_eq_elim H19); intros; subst; clear H19.
                  assert (Hsuba : j_var x (s1 ++ x :: s0)). apply (SQLSem2.j_var_sem_j_var _ _ _ H22).
                  assert (Hsubk : 0 < S (length tml0)). omega.
                  assert (Hfind : proj1_sig (Fin.to_nat (Fin_findpos x (s1 ++ x :: s0) Hsuba)) = 0 + length s1).
                  rewrite (Fin_findpos_tech _ _ _ _ _ eq_refl). reflexivity.
                  destruct (Hsub _ Hsuba _ Hsubk Hfind). destruct H1. 
                  pose (H' := H Fin.F1). clearbody H'.
                  replace (nth ul Fin.F1) with (nth ul (Fin.of_nat_lt Hsubk)) in H'.
                  destruct (not_veq_false _ _ H').
                  +++ rewrite H15 in H13. rewrite (Ev.j_var_sem_fun _ _ _ H1 _ H22) in H13. unfold Scm in eSt. rewrite H13 in eSt. discriminate eSt.
                  +++ assert (forall h0 (f0 : Fin.t (length (t::tml0))), h0 ~= h' -> f0 ~= (Fin.F1 : Fin.t (length (t::tml0)))-> nth (Stml0 h0) f0 = x0 h').
                      eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun _ t' tml' S' =>
                        forall h0 (f0 : Fin.t (length (t'::tml'))), h0 ~= h' -> f0 ~= (Fin.F1 : Fin.t (length (t::tml0))) -> nth (S' h0) f0 = x0 h') _ Html).
                      Unshelve. Focus 2. intros. apply (existT_eq_elim H25); intros; subst; clear H25. simpl.
                      rewrite (SQLSem2.j_tm_sem_fun _ _ _ H0 _ H19). reflexivity.
                      pose (H18' := (H18 h' Fin.F1 JMeq_refl JMeq_refl) : @nth Rel.V (S (@length pretm tml0)) (Stml0 h') (@Fin.F1 (@length pretm tml0)) = x0 h'); clearbody H18'.
                      rewrite H18' in H15. destruct H15. left. exact H15.
                      right. rewrite <- H15. rewrite <- H13.
                      rewrite (Ev.j_var_sem_fun _ _ _ H1 _ H22). reflexivity.
                  +++ reflexivity.
                  +++ pose (H0' := SQLSem2.j_tm_sem_weak _ ((s1++x::s0)::List.nil) _ _ H0); clearbody H0'.
                      rewrite (SQLSem2.j_tm_sem_fun _ _ _ H3 _ H0'). f_equal.
                      apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
                      transitivity (skipn (length (projT1 h'')) (projT1 h'' ++ projT1 h')).
                      rewrite Ev.skipn_append. reflexivity. f_equal. rewrite Ev.length_env. reflexivity.
               ** eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => 
                    exists St0', SQLSem2.j_tm_sem g t St0') _ Html). Unshelve.
                  simpl. intros. apply (existT_eq_elim H18); intros; subst; clear H18.
                  exists St1. exact H1.
         ++ discriminate eSc0.
       * generalize dependent H. generalize (@eq_refl _ ul).
         eapply (Vector.caseS' ul (fun ul0 => ul = ul0 -> (forall i : Fin.t (S (length tml0)),
            S3.is_bfalse (S3.veq (nth ul i) (nth (Stml0 h') i)) = false) ->
            S2.is_btrue (Sc2 (Ev.env_app _ _ h'' h')) = true)).
          intros u0 ul0 Hul. rewrite Hul. intro H. cut (length (s1 ++ x :: s0) = length (s1 ++ x :: Datatypes.nil) + length tml0).
          ++ intro Hcut. 
             assert (forall i : Fin.t (length tml0), 
               S3.is_bfalse (S3.veq (nth (cons Rel.V u0 (length tml0) ul0) (Fin.FS i)) 
                 (nth (cons _ (hd (Stml0 h')) _ (tl (Stml0 h'))) (Fin.FS i))) = false).
             intro i. pose (H (Fin.FS i)). simpl.
             replace (Stml0 h') with (cons _ (Vector.hd (Stml0 h')) _ (Vector.tl (Stml0 h'))) in e. simpl in e.
             exact e. rewrite <- Vector.eta. reflexivity.
             eapply (IH _ _ Hcut (fun h0 => tl (Stml0 h0))  _ ul0 _ h' h'' eq_refl _ _ _). Unshelve.
            -- simpl in H0. apply H0.
            -- rewrite <- app_assoc. reflexivity.
            -- generalize Hsub. rewrite Hul. apply cons_is_subenv'.
            -- exact H5.
            -- eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' =>
                        SQLSem2.j_tml_sem g' tml' (fun h0 => tl (S' h0))) _ Html). Unshelve.
               intros. simpl. apply (existT_eq_elim H15); intros; subst; clear H15.
               replace Stml1 with (fun h0 => tl (cons _ (St h0) _ (Stml1 h0))) in H3. exact H3.
               extensionality h0. reflexivity.
          ++ do 2 rewrite app_length. simpl. rewrite Hlen0. omega.
  Qed.

  Lemma eq_is_subenv' {m} (ul : Rel.T m) {n} (vl : Rel.T n) {s} {g} (h : Ev.env (s::g)) : 
    m = n ->
    forall k (Hul : length s = k + m) (Hvl : length s = k + n), ul ~= vl -> is_subenv' ul Hul h -> is_subenv' vl Hvl h.
  Proof.
    intro. generalize ul; clear ul; rewrite H; intro ul.
    intros k Hul Hvl e. generalize Hul; clear Hul; rewrite e; intro Hul. intro Hsub.
    unfold is_subenv'. intros. destruct (Hsub a Ha k0 Hk H0). eexists. exact H1.
  Qed.

  (* XXX: SQLSem2/3 *)
  Lemma tech_sem_cndeq d g t1 t2 Sc St1 St2 : 
    SQLSem2.j_cond_sem d g (cndeq t1 t2) Sc ->
    SQLSem2.j_tm_sem g t1 St1 ->
    SQLSem2.j_tm_sem g t2 St2 ->
    forall h, Sc h = S2.veq (St1 h) (St2 h).
  Proof.
    unfold cndeq. intros. inversion H. 
    apply (existT_eq_elim H5). intros; subst; clear H5 H8.
    apply (existT_eq_elim H7); intros; subst. clear H7 H2.
    inversion H4.
    apply (existT_eq_elim H6). intros; subst; clear H6 H8.
    inversion H7.
    apply (existT_eq_elim H8). intros; subst; clear H8 H10.
    rewrite (SQLSem2.j_tm_sem_fun _ _ _ H5 _ H0). rewrite (SQLSem2.j_tm_sem_fun _ _ _ H6 _ H1).
    inversion H9. apply (existT_eq_elim H3). intros; subst; clear H2 H3.
    apply S2.sem_bpred_elim.
    + simpl. intro. apply bind_elim.
      - intro. simpl. apply bind_elim.
        * simpl. intros y0 Hy0 Hy. apply bind_elim.
          ++ intros y1 Hy1 Hcl Hlencl. injection Hcl. injection Hy. clear Hcl Hy. intros Hy Hcl. subst.
             unfold nth_lt. simpl. unfold S2.veq. rewrite Hy0, Hy1. reflexivity.
          ++ intros _ Hfalse. discriminate Hfalse.
        * intros _ Hfalse. discriminate Hfalse.
      - intros _ Hfalse. discriminate Hfalse.
    + simpl. apply bind_elim.
      - intro. apply bind_elim.
        * simpl. intros y0 Hy0 Hy. apply bind_elim.
          ++ intros y1 _ Hfalse. discriminate Hfalse.
          ++ intros H2 _. rewrite H2, Hy0. reflexivity.
        * intros _ Hfalse. discriminate Hfalse.
      - apply bind_elim.
        * intros y _ Hfalse. discriminate Hfalse.
        * intro. rewrite H2. unfold S2.veq. destruct (St1 h); intuition.
  Qed.

  (* XXX: SQLSem2/3 *)
  Lemma tech_term_eq d g t a s1 al Sa St Sc h h0 x :
    SQLSem2.j_tm_sem g t St ->
    SQLSem2.j_tm_sem (((s1 ++ a:: List.nil) ++ al)::g) (tmvar (0,a)) Sa -> Sa (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h) = x ->
    SQLSem2.j_cond_sem d (((s1 ++ a :: Datatypes.nil) ++ al) :: g)
       ((tmvar (0, a) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a)))) Sc ->
    Sc (Ev.env_app (((s1 ++ a :: List.nil) ++ al) :: List.nil) _ h0 h) = negb (S3.is_bfalse (S3.veq x (St h))).
  Proof.
    intros H Ha Hx H0. apply Bool.eq_iff_eq_true. eapply (@coimpl_trans _ (S3.is_bfalse (S3.veq x (St h)) = false)).
      Focus 2. destruct (S3.is_bfalse (S3.veq x (St h))); intuition.
    apply coimpl_sym.
    eapply (coimpl_trans (not_veq_false' _ _)).
    split.
    + inversion H0. apply (existT_eq_elim H4); intros; subst; clear H0 H4 H7.
      inversion H5. apply (existT_eq_elim H4); intros; subst; clear H4 H5 H7.
      inversion H6. apply (existT_eq_elim H4); intros; subst; clear H4 H6 H8.
      inversion H5. apply (existT_eq_elim H6); intros; subst; clear H5 H6 H8.
      assert (SQLSem2.j_tm_sem ((((s1 ++ a :: List.nil) ++ al) :: List.nil) ++ g) (tm_lift t 1) (fun h => St (Ev.subenv2 h))).
        apply SQLSem2.j_tm_sem_weak. exact H.
      rewrite (SQLSem2.j_tm_sem_fun _ _ _ H3 _ H0).
      replace (Ev.subenv2 (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h)) with h.
        Focus 2. apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
        transitivity (skipn (length (projT1 h0)) (projT1 h0 ++ projT1 h)).
        rewrite Ev.skipn_append. reflexivity.
        f_equal. rewrite Ev.length_env. reflexivity.
      destruct H9.
      - replace (St0 (Ev.env_app _ _ h0 h)) with null. reflexivity.
        rewrite (SQLSem2.j_tm_sem_fun _ _ _ H2 _ Ha). rewrite H1. reflexivity.
      - destruct H1.
        * unfold S2.bor. apply Bool.orb_true_intro. right. rewrite H1. reflexivity.
        * decompose record H1. rewrite H5. replace (St0 (Ev.env_app _ _ h0 h)) with (Some x0). simpl.
          replace (Sc0 (Ev.env_app _ _ h0 h)) with (S2.veq (Some x0) (Some x)).
          simpl. apply Db.BaseConst_eqb_eq. symmetry. apply Db.BaseConst_eqb_eq. exact H8.
          rewrite <- H5. rewrite <- H4.
          replace (St h) with (St (Ev.subenv2 (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h))).
          symmetry. apply (tech_sem_cndeq _ _ _ _ _ _ _ H7 H0 Ha).
          f_equal. apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
          transitivity (skipn (length (projT1 h0)) (projT1 h0 ++ projT1 h)).
          rewrite Ev.length_env. reflexivity.
          rewrite Ev.skipn_append. reflexivity.
          rewrite (SQLSem2.j_tm_sem_fun _ _ _ H2 _ Ha). rewrite H4.
          f_equal. symmetry. apply Db.BaseConst_eqb_eq. exact H8.
    + inversion H0. apply (existT_eq_elim H4); intros; subst; clear H0 H4 H7.
      inversion H5. apply (existT_eq_elim H4); intros; subst; clear H4 H5 H7.
      inversion H6. apply (existT_eq_elim H4); intros; subst; clear H4 H6 H8.
      inversion H5. apply (existT_eq_elim H6); intros; subst; clear H5 H6 H8.
      assert (SQLSem2.j_tm_sem ((((s1 ++ a :: List.nil) ++ al) :: List.nil) ++ g) (tm_lift t 1) (fun h => St (Ev.subenv2 h))).
        apply SQLSem2.j_tm_sem_weak. exact H.
      rewrite (SQLSem2.j_tm_sem_fun _ _ _ H3 _ H0) in H9.
      replace (Ev.subenv2 (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h)) with h in H9.
        Focus 2. apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
        transitivity (skipn (length (projT1 h0)) (projT1 h0 ++ projT1 h)).
        rewrite Ev.skipn_append. reflexivity.
        f_equal. rewrite Ev.length_env. reflexivity.
      unfold S2.bor, S2.of_bool in H9. eapply (bool_orb_elim _ _ _ _ _ H9). Unshelve.
      - destruct (St0 (Ev.env_app _ _ h0 h)) eqn:eSt0.
        * intro Hfalse. discriminate Hfalse.
        * intros _. left. unfold null. rewrite <- eSt0.
          rewrite (SQLSem2.j_tm_sem_fun _ _ _ Ha _ H2). reflexivity.
      - apply bool_orb_elim.
        * destruct (St h) eqn:eSt. intro Hfalse; discriminate Hfalse. intros _. right. left. reflexivity.
        * replace (Sc0 (Ev.env_app _ _ h0 h)) with (S2.veq (St h) (St0 (Ev.env_app _ _ h0 h))).
          unfold S2.veq. destruct (St h) eqn:eSt.
          ++ destruct (St0 (Ev.env_app _ _ h0 h)) eqn:eSt0.
            -- intro. right. right. exists b. exists b0. intuition.
               rewrite (SQLSem2.j_tm_sem_fun _ _ _ Ha _ H2). rewrite eSt0. 
               symmetry. f_equal. apply Db.BaseConst_eqb_eq. exact H1.
               f_equal. apply Db.BaseConst_eqb_eq. exact H1.
            -- intro Hfalse. discriminate Hfalse.
          ++ intro Hfalse. discriminate Hfalse.
          ++ symmetry. 
             replace (St h) with (St (Ev.subenv2 (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h))).
             apply (tech_sem_cndeq _ _ _ _ _ _ _ H7 H0 H2).
             f_equal. apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
             transitivity (skipn (length (projT1 h0)) (projT1 h0 ++ projT1 h)).
             rewrite Ev.length_env. reflexivity.
             rewrite Ev.skipn_append. reflexivity.
  Qed.

  Lemma j_var_sem_tech : forall a s1 s2 (x : Rel.T (S (length s2))) (y : Rel.T (length s1)) e,
    forall Sa,
    Ev.j_var_sem (s1 ++ a :: s2) a Sa ->
    Sa (Ev.env_of_tuple ((s1++a::s2)::List.nil) (cast _ _ e (Vector.append y x))) ~= hd x.
  Proof.
    intros a s1. induction s1; simpl; intuition.
    + inversion H. Focus 2. contradiction H4. reflexivity.
      rewrite <- (existT_projT2_eq _ _ _ H4). clear H4. subst.
      unfold Ev.env_hd. apply unopt_elim.
      unfold Ev.env_of_tuple, Ev.env_app. simpl. intro.
      eapply (split_ind _ (fun m n p => hd_error (to_list (fst (let (v1,v2) := p in 
        (cons Rel.V (hd (cast _ _ e (append y x))) m v1, v2))) ++ List.nil) = Some y0 -> y0 ~= hd x)).
      simpl. intros. injection H2. intro. rewrite <- H4.
      eapply (f_JMequal hd hd). Unshelve. rewrite plus_0_r. reflexivity. apply cast_JMeq.
      apply (case0 (fun y0 => append y0 x ~= x)). reflexivity.
      rewrite plus_0_r. reflexivity.
      rewrite plus_0_r. reflexivity.
    + inversion H. contradiction H3. apply in_or_app. right. left. reflexivity.
      rewrite <- (existT_projT2_eq _ _ _ H2). clear H2. subst.
      eapply (JMeq_trans _ (IHs1 _ _ (tl y) _ _ H5)). Unshelve.
      Focus 2. simpl. rewrite plus_0_r. rewrite app_length. reflexivity.
      apply eq_JMeq. f_equal. apply Ev.env_eq.
      unfold Ev.env_tl. simpl.
      eapply (split_ind _ (fun m n p =>
        List.tl (to_list (fst (let (v1,v2) := p in (cons _ (hd (cast _ _ e (append y x))) _ v1, v2))) ++ List.nil)
        = _)).
      intros. eapply (split_ind _ (fun m n p => _ = to_list (fst p) ++ List.nil)).
      simpl. intros. f_equal.
      transitivity (to_list v1). reflexivity.
      f_equal. apply JMeq_eq. symmetry. generalize dependent H1.
      apply (case0 (fun w => cast _ _ _ (append (tl y) x) = append v0 w -> v0 ~= v1)). intro H1.
      assert (v0 ~= append (tl y) x). 
        symmetry. eapply (JMeq_trans _ (vector_append_nil_r v0)). Unshelve. Focus 2.
        rewrite <- H1. symmetry. apply cast_JMeq. reflexivity.
      apply (JMeq_trans H2). generalize dependent H0.
      apply (case0 (fun w => tl (cast _ _ _ (append y x)) = append v1 w -> append (tl y) x ~= v1)). intro H0.
      assert (v1 ~= tl (append y x)). 
        symmetry. eapply (JMeq_trans _ (vector_append_nil_r v1)). Unshelve. Focus 2.
        rewrite <- H0. eapply (f_JMequal tl tl). Unshelve. rewrite plus_0_r, app_length. reflexivity.
        symmetry. apply cast_JMeq. reflexivity.
        rewrite plus_0_r, app_length. reflexivity.
        rewrite plus_0_r, app_length. reflexivity.
      symmetry. apply (JMeq_trans H3).
      apply (caseS (fun nw w => tl (append w x) ~= append (tl w) x)).
      simpl. intuition.
  Qed.

  (* XXX: SQLSem2/3 *)
  Lemma tech_vec_append_tmvar : forall a s1 s2 (x:Rel.T (S (length s2))) (y:Rel.T (length s1)) e g h,
    forall Sa,
    SQLSem2.j_tm_sem ((s1++a::s2)::g) (tmvar (0,a)) Sa ->
    Sa (Ev.env_app _ g (Ev.env_of_tuple ((s1++a::s2)::List.nil) (cast _ _ e (Vector.append y x))) h) = hd x.
  Proof.
    intros. inversion H. subst. inversion H3. apply (existT_eq_elim H1). intros; subst; clear H1 H6.
    apply JMeq_eq. eapply (JMeq_trans _ (j_var_sem_tech _ _ _ x y e _ H5)). Unshelve.
    apply eq_JMeq. f_equal. apply Ev.env_eq. unfold Ev.subenv1, Ev.env_app. simpl.
    apply (split_ind _ (fun m n p => firstn _ ((to_list (fst p) ++ List.nil) ++ projT1 h) 
      = to_list (fst p) ++ List.nil)).
    simpl. intros. do 2 rewrite app_nil_r.
    transitivity (firstn (length (to_list v1) + 0) (to_list v1 ++ projT1 h)).
    + f_equal. rewrite length_to_list, plus_0_r. reflexivity.
    + rewrite firstn_app_2. simpl. rewrite app_nil_r. reflexivity.
  Qed.

  (* XXX: SQLSem2/3 *)
  Lemma tech_sem_not_exists' d g tml s ul1 (ul2 : Rel.T (length tml)) Sc Stml h :
    length s = length tml -> ul1 ~= ul2 ->
    SQLSem2.j_cond_sem d (s :: g)%list 
      (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s)) 
      Sc ->
    SQLSem2.j_tml_sem g tml Stml ->
    Sc (Ev.env_app _ _ (Ev.env_of_tuple (s :: List.nil) ul1) h)
    = fold_right2 (fun (u0 v0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool)
        true (length tml) ul2 (Stml h).
  Proof.
    intros Hlen Heq Hc Html.
    enough 
      (forall s1, 
         forall ul1 ul2 (ul0 : Rel.T (length s1)), ul1 ~= Vector.append ul0 ul2 -> 
         forall Stml, SQLSem2.j_tml_sem g tml Stml -> 
         forall Sc, SQLSem2.j_cond_sem d ((s1++s)::g) 
          (List.fold_right (fun (ta:pretm*Name) acc =>
              let (t, a) := ta in
              ((tmvar (0, a) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a)))) AND acc) 
             (TRUE) (combine tml s)) Sc ->
        Sc (Ev.env_app ((s1++s) :: Datatypes.nil) g (Ev.env_of_tuple ((s1++s) :: Datatypes.nil) ul1) h) = 
        fold_right2 (fun u0 v0 acc => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true (length tml) ul2 (Stml h)).
    apply (H List.nil ul1 ul2 (Vector.nil _) Heq _ Html _ Hc).
    clear ul1 ul2 Sc Stml Heq Hc Html.
    eapply (list_ind2 _ _ (fun s0 tml0 =>
        forall s1 ul1 ul2 ul0, ul1 ~= append ul0 ul2 -> 
        forall Stml, SQLSem2.j_tml_sem g tml0 Stml -> 
        forall Sc, SQLSem2.j_cond_sem d ((s1++s0) :: g)
          (List.fold_right
             (fun (ta : pretm * Name) (acc : precond) =>
              let (t, a) := ta in
              ((tmvar (0, a) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a)))) AND acc) 
             (TRUE) (combine tml0 s0)) Sc ->
        Sc (Ev.env_app ((s1 ++ s0) :: Datatypes.nil) g (Ev.env_of_tuple ((s1++s0) :: Datatypes.nil) ul1) h) = 
        fold_right2 (fun u0 v0 acc => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true (length tml0) ul2 (Stml h))
      _ _ s tml Hlen). Unshelve.
    + hnf. intros. inversion H1. apply (existT_eq_elim H3); intros; subst; clear H3 H4.
      eapply (case0 (fun ul => S2.btrue = fold_right2 (fun u0 v0 acc => 
       (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true (length (List.nil)) ul (Stml h))).
      eapply (case0 (fun ul => S2.btrue = fold_right2 (fun u0 v0 acc => 
       (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true (length (List.nil)) (nil _) ul)).
      reflexivity.
    + hnf. intros. rewrite (Vector.eta ul2).
      inversion H2. apply (existT_eq_elim H7); intros; subst; clear H7 H9.
      transitivity ((fold_right2 (fun u0 v0 acc => 
        (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true (length bl) (tl ul2) (Stml0 h)
        && negb (S3.is_bfalse (S3.veq (hd ul2) (St h))))%bool).
      Focus 2. reflexivity.
      pose (s1' := s1 ++ (a::List.nil)).
      enough (es1 : length (s1 ++ a :: al) + 0 = length (s1'++al) + 0).
      pose (ul1' := cast _ _ (f_equal Rel.T es1) ul1).
      pose (ul2' := tl ul2).
      enough (es0 : length s1 + 1 = length s1').
      pose (ul0' := cast _ _ (f_equal Rel.T es0) (append ul0 (cons _ (hd ul2) _ (Vector.nil _)))).
      enough (Heq' : ul1' ~= append ul0' ul2').
      enough (exists (h' : Ev.env (((s1++(a::List.nil))++al)::List.nil)),
        Ev.env_of_tuple ((s1 ++ a :: al) :: Datatypes.nil) ul1 ~= h'). decompose record H4. clear H4.
      enough (exists Sc1 Sc2, 
        SQLSem2.j_cond_sem d (((s1++(a::List.nil))++al)::g) ((tmvar (0,a) IS NULL) OR 
          ((tm_lift b 1 IS NULL) OR cndeq (tm_lift b 1) (tmvar (0, a)))) Sc1 /\
        SQLSem2.j_cond_sem d (((s1++(a::List.nil))++al)::g) 
          (List.fold_right (fun (ta : pretm * Name) acc =>
           let (t, a) := ta in
           ((tmvar (0, a) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a)))) AND acc)
           (TRUE) (combine bl al)) Sc2 /\
        forall h' h'', h' ~= h'' -> (Sc h' = Sc1 h'' && Sc2 h'')%bool). decompose record H4. clear H4.
      transitivity ((x0 (Ev.env_app _ _ x h) && x1 (Ev.env_app _ _ x h))%bool).
        apply H11.
        eapply (f_JMequal (Ev.env_app ((s1++a::al)::List.nil) g (Ev.env_of_tuple ((s1++a::al)::List.nil) ul1)) 
                 (Ev.env_app (((s1++a::List.nil)++al)::List.nil) g x)). Unshelve.
        eapply (f_JMequal (Ev.env_app ((s1++a::al)::List.nil) g) 
                 (Ev.env_app (((s1++a::List.nil)++al)::List.nil) g)). Unshelve.
        rewrite <- app_assoc. reflexivity. exact H5. reflexivity.
      rewrite Bool.andb_comm. f_equal. 
      transitivity (fold_right2 (fun u0 v0 acc => 
        (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool) true (length bl) ul2' (Stml0 h)).
      rewrite <- (H0 s1' ul1' ul2' ul0' Heq' _ H8 _ H9).
      apply f_equal. f_equal. apply JMeq_eq. symmetry. eapply (JMeq_trans _ H5). Unshelve.
      reflexivity. assert (Ha : exists Sa, SQLSem2.j_tm_sem (((s1 ++ a :: Datatypes.nil) ++ al) :: g) (tmvar (0,a)) Sa).
        inversion H7. apply (existT_eq_elim H13). intros; subst; clear H13 H16.
        inversion H14. apply (existT_eq_elim H16). intros; subst; clear H16 H17. exists St0. exact H12.
      destruct Ha as [Sa Ha]. eapply (tech_term_eq _ _ _ _ _ _ _ _ _ _ _ _ H6 Ha _ H7). Unshelve. Focus 11.
      pose (ul2'' := cast _ _ (f_equal (fun n => Rel.T (S n)) (eq_sym H)) ul2).
      assert (e : t Rel.V (length s1 + S (length al)) =
        Rel.T (list_sum (List.map (length (A:=Name)) ((s1 ++ a :: al) :: Datatypes.nil)))).
        simpl. rewrite app_length, plus_0_r. reflexivity.
      generalize dependent Sa. generalize dependent x.
      replace ((s1 ++ a :: Datatypes.nil) ++ al) with (s1++a::al).
      intros.
      transitivity (Sa (Ev.env_app _ _ (Ev.env_of_tuple _ (cast _ _ e (Vector.append ul0 ul2''))) h)).
      f_equal. f_equal. symmetry in H5. apply JMeq_eq. apply (JMeq_trans H5).
      apply eq_JMeq. f_equal. apply JMeq_eq. symmetry. apply cast_JMeq.
      symmetry. apply (JMeq_trans H1).
      eapply (f_JMequal (append _) (append _)). Unshelve. rewrite H. reflexivity.
      symmetry. apply cast_JMeq. reflexivity.
      rewrite (tech_vec_append_tmvar _ _ _ ul2'' ul0 _ g h Sa).
      apply JMeq_eq. eapply (f_JMequal hd hd). Unshelve. rewrite H. reflexivity.
      apply cast_JMeq. reflexivity. exact Ha.
      rewrite <- app_assoc. reflexivity. rewrite H. reflexivity.
      rewrite H. reflexivity.
      rewrite H. reflexivity.
      rewrite H. reflexivity.
      simpl in H3. inversion H3. apply (existT_eq_elim H10); intros; subst; clear H10 H13.
      rewrite <- app_assoc. exists Sc1. exists Sc2. split. exact H11. split. exact H12.
      intros. rewrite H4. reflexivity.
      rewrite <- app_assoc. eexists. reflexivity.
      apply cast_JMeq. apply (JMeq_trans H1). unfold ul0', ul2'.
      apply (JMeq_trans (vector_append_cons ul0 ul2)). 
      eapply (f_JMequal (append _) (append _)). Unshelve.
      eapply (f_JMequal append append). Unshelve. 
      unfold s1'. rewrite app_length. reflexivity.
      symmetry. apply cast_JMeq. reflexivity. reflexivity.
      unfold s1'. rewrite app_length. reflexivity.
      unfold s1'. repeat rewrite app_length. simpl. omega.
      reflexivity.
      rewrite <- app_assoc. reflexivity.
      rewrite <- app_assoc. reflexivity.
      rewrite <- app_assoc. reflexivity.
      eapply (f_JMequal (Ev.env_of_tuple _) (Ev.env_of_tuple _)). Unshelve.
      rewrite <- app_assoc. reflexivity.
      apply cast_JMeq. reflexivity.
      reflexivity.
      unfold s1'. rewrite app_length. reflexivity.
      unfold s1'. rewrite app_length. reflexivity.
      unfold s1'. rewrite app_length. reflexivity.
      rewrite <- app_assoc. reflexivity.
      rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma tech_j_var_sem : forall a s, List.In a s -> NoDup s -> 
    exists Sa : Ev.env (s :: Datatypes.nil) -> Value, Ev.j_var_sem s a Sa.
  Proof.
    intros a s. elim s.
    + intro H; destruct H.
    + intros. inversion H1. destruct H0. 
      - subst. eexists. constructor. exact H4.
      - destruct (H H0 H5). subst. eexists. constructor. intro. contradiction H4. rewrite H2. exact H0.
        exact H6.
  Qed.

  Lemma tech_j_cond_fold_vect' d s0 n (s : Vector.t Name n) g (tml : Vector.t pretm n) :
    List.NoDup s0 -> forall Stml, SQLSem2.j_tml_sem g (to_list tml) Stml -> incl (to_list s) s0 ->
    exists Sc : Ev.env ((s0 :: Datatypes.nil) ++ g) -> S2.B,
    SQLSem2.j_cond_sem d ((s0 :: Datatypes.nil) ++ g)
      (List.fold_right
       (fun (ta : pretm * Name) (acc : precond) =>
        let (t, a) := ta in
        ((tmvar (0, a) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a)))) AND acc) 
       (TRUE) (combine (VectorDef.to_list tml) (VectorDef.to_list s))) Sc.
  Proof.
    intros Hnodup.
    eapply (Vector.rect2 (fun n s' tml' => 
      forall Stml, SQLSem2.j_tml_sem g (to_list tml') Stml -> incl (to_list s') s0 -> 
      exists Sc,
      SQLSem2.j_cond_sem d ((s0 :: List.nil) ++ g) (List.fold_right
        (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
        (combine (to_list tml') (to_list s'))) Sc)
      _ _ s tml). Unshelve.
    + simpl. intros. eexists. constructor. 
    + simpl. intros m s' tml' IH a0 t0 Stml Html' Hincl.
      unfold to_list in Html'. 
      eapply (SQLSem2.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => _) _ Html'). Unshelve. simpl. intros.
      apply (existT_eq_elim H3); intros; subst; clear H3 H5.
      enough (incl (to_list s') s0). destruct (IH _ H4 H0).
      enough (exists Sa0, Ev.j_var_sem s0 a0 Sa0). destruct H3.
      eexists. constructor. Focus 2. exact H1.
      constructor. constructor. constructor. constructor. exact H3.
      constructor. constructor. eapply (SQLSem2.j_tm_sem_weak g (s0::List.nil) _ _ H2).
      constructor. constructor. eapply (SQLSem2.j_tm_sem_weak g (s0::List.nil) _ _ H2).
      constructor. constructor. constructor. exact H3. constructor.
      apply tech_j_var_sem. apply Hincl. left. reflexivity. exact Hnodup.
      intros x Hx. apply Hincl. right. exact Hx.
      Unshelve. reflexivity.
  Qed.

  Lemma tech_j_cond_fold' d s0 s g tml :
    length tml = length s -> List.NoDup s0 -> forall Stml, SQLSem2.j_tml_sem g tml Stml-> incl s s0 ->
    exists Sc,
    SQLSem2.j_cond_sem d ((s0 :: Datatypes.nil) ++ g) (List.fold_right
     (fun (ta : pretm * Name) (acc : precond) => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc)
     (TRUE) (combine tml s)) Sc.
  Proof.
    intro Hlen. rewrite <- (to_list_of_list_opp tml). rewrite <- (to_list_of_list_opp s).
    generalize (of_list tml) (of_list s). rewrite Hlen. intros vtml vs. apply tech_j_cond_fold_vect'.
  Qed.

  Lemma cond_sem_not_ex_selstar' d g q s s0 tml Hs0 (Hlens : length s = length s0) 
     Sff Sq Sc (Hff : SQLSem2.j_cond_sem d g (NOT (EXISTS (SELECT * FROM ((tbquery (ttquery d q), s0) :: List.nil)::List.nil
      WHERE List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
              (TRUE) (combine tml s0)))) Sff)
     (Hq : SQLSem2.j_q_sem d g s (ttquery d q) Sq) 
     (Hc : SQLSem2.j_cond_sem d (s0 :: g)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s0)) Sc) h :
    S2.is_btrue (Sff h) =
    negb (0 <? Rel.card (Rel.sel (Sq h) (fun Vl => S2.is_btrue (Sc (Ev.env_app _ _ (Ev.env_of_tuple (s0 :: List.nil) (cast _ _ Hs0 Vl)) h))))).
  Proof.
    cut (forall (h0 : Ev.env g), h0 ~= h -> 
      S2.is_btrue (Sff h0) =
      negb (0 <? Rel.card (Rel.sel (Sq h) (fun Vl => 
        S2.is_btrue (Sc (Ev.env_app _ _ (Ev.env_of_tuple (s0 :: List.nil) (cast _ _ Hs0 Vl)) h)))))).
    intro Hcut. apply (Hcut h). reflexivity. inversion Hff. apply (existT_eq_elim H1); intros; subst. clear Hff H3 H1.
    cut (forall b1 b2, S2.is_btrue b1 = b2 -> S2.is_btrue (S2.bneg b1) = negb b2).
    Focus 2. unfold S2.is_btrue, S2.bneg. intros. rewrite H. reflexivity.
    intro Hcut. apply Hcut. inversion H2. apply (existT_eq_elim H1); intros; subst. clear H2 H1 H4.
    inversion H3. apply (existT_eq_elim H5); intros; subst. clear H3 H5 H7.
    inversion H2. apply (existT_eq_elim H7); intros; subst. clear H2 H4 H7 H9.
    apply (existT_eq_elim (JMeq_eq H10)); intros; subst. clear H10 H.
    inversion H5. apply (existT_eq_elim H9); intros; subst. clear H5 H9 H4 H12.
    apply (existT_eq_elim (JMeq_eq H13)); intros; subst. clear H13 H.
    eapply (SQLSem2.j_nil_btb_sem _ _ _ _ _ _ H10). Unshelve. intros; subst. rewrite <- H2. clear H10 H2.
    inversion H7. apply (existT_eq_elim H2); intros; subst. clear H7 H2 H4.
    apply (existT_eq_elim (JMeq_eq H5)); intros; subst. clear H5 H.
    eapply (SQLSem2.j_nil_btbl_sem _ _ _ _ _ _ H8). Unshelve.
    intros; subst. rewrite <- H2.
    transitivity (0 <?
      Rel.card
        (Rel.sel
           (Rel.rsum
              (cast (Rel.R (length s1 + list_sum (List.map (length (A:=Name)) Datatypes.nil)))
                 (Rel.R (length s0 + list_sum (List.map (length (A:=Name)) Datatypes.nil))) e0
                 (Rel.times (ST h) Rel.Rone))
              (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) (s0 :: Datatypes.nil))) =>
               cast
                 (Rel.R
                    (list_sum (List.map (length (A:=Name)) Datatypes.nil) +
                     list_sum (List.map (length (A:=Name)) (s0 :: Datatypes.nil))))
                 (Rel.R (list_sum (List.map (length (A:=Name)) (Datatypes.nil ++ s0 :: Datatypes.nil)))) e
                 (Rel.times Rel.Rone (Rel.Rsingle Vl))))
           (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) (Datatypes.nil ++ s0 :: Datatypes.nil))) =>
            S2.is_btrue
              (Sc0
                 (Evl.env_app (Datatypes.nil ++ s0 :: Datatypes.nil) g
                    (Evl.env_of_tuple (Datatypes.nil ++ s0 :: Datatypes.nil) Vl) h))))).
    reflexivity. f_equal.
    apply eq_card_dep. rewrite Hlens. simpl. omega.
    eapply (f_JMequal (Rel.sel _) (Rel.sel _)).
    eapply (f_JMequal (@Rel.sel _) (@Rel.sel _)). rewrite Hlens. simpl. rewrite plus_0_r. reflexivity.
    destruct (SQLSem2.jq_sem_fun_dep _ _ _ _ _ Hq _ _ _ _ eq_refl eq_refl H3). subst.
    simpl. apply (@trans_JMeq _ _ _ _ (Rel.rsum (ST h) (fun Vl => Rel.Rsingle Vl))).
      apply eq_rsum_dep. rewrite H11; omega. rewrite H11; omega. apply cast_JMeq. apply Rel_times_Rone.
      apply funext_JMeq. rewrite H11, <- plus_n_O; reflexivity. rewrite H11, <- plus_n_O; reflexivity.
      intros. apply cast_JMeq. apply (trans_JMeq (Rel_Rone_times _ (Rel.Rsingle x))).
      generalize dependent x. rewrite <- (plus_n_O (length s0)), <- H11. intros. rewrite H. reflexivity.
    eapply (trans_JMeq (rsum_id _ _ _ _ _)). rewrite H0. reflexivity.
    apply funext_JMeq; intros.
      simpl. rewrite <- plus_n_O, Hlens. reflexivity. reflexivity.
    generalize (SQLSem2.jc_sem_fun_dep _ _ _ _ H6 _ _ _ eq_refl eq_refl Hc); intro.
    rewrite H0. apply eq_JMeq. f_equal. f_equal.
    f_equal. f_equal. symmetry. apply JMeq_eq. apply cast_JMeq. symmetry. exact H.
    Unshelve.
    simpl. rewrite Hlens, <- plus_n_O. reflexivity.
    simpl. rewrite Hlens, <- plus_n_O. reflexivity.
    simpl. rewrite Hlens, <- plus_n_O. reflexivity.
    simpl. rewrite Hlens, <- plus_n_O. reflexivity.
    intro; reflexivity.
  Qed.

  Lemma sem_tm_bool_to_tribool {g} {t} {St} :
    SQLSem3.j_tm_sem g t St -> SQLSem2.j_tm_sem g t St.
  Proof.
    intro; induction H; constructor; intuition.
  Qed.

  Lemma sem_tml_bool_to_tribool {g} {tl} {Stl} :
    SQLSem3.j_tml_sem g tl Stl -> SQLSem2.j_tml_sem g tl Stl.
  Proof.
    intro; induction H; constructor; intuition. apply sem_tm_bool_to_tribool. exact H.
  Qed.

  Lemma list_sum_app : forall l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
  Proof.
    intros. induction l1; simpl; intuition.

  Qed.

  Theorem sem_bool_to_tribool : forall d G Q s SQ3,
    SQLSem3.j_q_sem d G s Q SQ3 -> 
    exists SQ2, SQLSem2.j_q_sem d G s (ttquery d Q) SQ2 /\
    forall h, SQ3 h ~= SQ2 h.
  Proof.
    intros d G Q s SQ3 H.
    eapply (SQLSem3.jqs_ind_mut _
          (fun G0 s0 Q0 S0 _ => exists S1, SQLSem2.j_q_sem d G0 s0 (ttquery d Q0) S1 /\ forall h, S0 h ~= S1 h)
          (fun G0 s0 T0 S0 _ => exists S1, SQLSem2.j_tb_sem d G0 s0 (tttable d T0) S1 /\ forall h, S0 h ~= S1 h)
          (fun G0 c0 S0 _ => exists S1 S2, 
            SQLSem2.j_cond_sem d G0 (ttcond d c0) S1 /\ SQLSem2.j_cond_sem d G0 (ffcond d c0) S2 /\
            (forall h, S3.is_btrue (S0 h) = S2.is_btrue (S1 h)) /\ 
            (forall h, S3.is_btrue (negtb (S0 h)) = S2.is_btrue (S2 h)))
          (fun G0 G1 btb S0 _ => 
            exists S1, SQLSem2.j_btb_sem d G0 G1 (List.map (fun bT => (tttable d (fst bT), snd bT)) btb) S1 /\ 
            forall h, S0 h ~= S1 h)
          (fun G0 G1 btbl S0 _ => 
            exists S1, SQLSem2.j_btbl_sem d G0 G1 (List.map (fun btb => 
              List.map (fun bT => (tttable d (fst bT), snd bT)) btb) btbl) S1 /\ 
            forall h, S0 h ~= S1 h)
          (fun G0 Q0 S0 _ => exists S1, SQLSem2.j_in_q_sem d G0 (ttquery d Q0) S1 /\ forall h, S0 h ~= S1 h)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  Unshelve.
  (** mutual induction cases: query *)
  + simpl. intros G0 b tml btbl c G1 Sbtbl Sc Stml s0 e Hbtb IHbtbl Hc IHc Html.
    decompose record IHbtbl. decompose record IHc.
    eexists. split. eapply (SQLSem2.jqs_sel _ _ _ _ _ _ _ _ _ _ _ e H1 H0 (sem_tml_bool_to_tribool Html)).
    exact e0.
    intro. simpl. destruct b.
    - apply eq_JMeq. f_equal. apply JMeq_eq. apply cast_JMeq. symmetry. apply cast_JMeq. rewrite H2.
      eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMeq _ _ (@Rel.sum _ _)). apply JMeq_eq. eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
      reflexivity. reflexivity. reflexivity.
    - apply cast_JMeq. symmetry. apply cast_JMeq. rewrite H2.
      eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMeq _ _ (@Rel.sum _ _)). apply JMeq_eq. eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
      reflexivity. reflexivity. reflexivity.
  + simpl. intros G0 b btb c s0 G1 Sbtb Sc Stml e Hbtb IHbtb Hc IHc Html.
    decompose record IHbtb. decompose record IHc.
    eexists. split. eapply (SQLSem2.jqs_selstar _ _ _ _ _ _ _ _ _ _ e H1 H0 (sem_tml_bool_to_tribool Html)).
    exact e0.
    intro. simpl. destruct b.
    - apply eq_JMeq. f_equal. apply JMeq_eq. apply cast_JMeq. symmetry. apply cast_JMeq. rewrite H2.
      eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMeq _ _ (@Rel.sum _ _)). apply JMeq_eq. eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
      reflexivity. reflexivity. reflexivity.
    - apply cast_JMeq. symmetry. apply cast_JMeq. rewrite H2.
      eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMeq _ _ (@Rel.sum _ _)). apply JMeq_eq. eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
      reflexivity. reflexivity. reflexivity.
  + simpl. intros G0 b q1 q2 s0 S1 S2 Hq1 IHq1 Hq2 IHq2.
    decompose record IHq1. decompose record IHq2.
    eexists. split. eapply (SQLSem2.jqs_union _ _ _ _ _ _ _ _ H1 H3).
    intro. rewrite H2, H4. reflexivity.
  + simpl. intros G0 b q1 q2 s0 S1 S2 Hq1 IHq1 Hq2 IHq2.
    decompose record IHq1. decompose record IHq2.
    eexists. split. eapply (SQLSem2.jqs_inters _ _ _ _ _ _ _ _ H1 H3).
    intro. rewrite H2, H4. reflexivity.
  + simpl. intros G0 b q1 q2 s0 S1 S2 Hq1 IHq1 Hq2 IHq2.
    decompose record IHq1. decompose record IHq2.
    eexists. split. eapply (SQLSem2.jqs_except _ _ _ _ _ _ _ _ H1 H3).
    intro. rewrite H2, H4. reflexivity.
  (** mutual induction cases: tb *)
  + simpl. intros G0 x s0 e. eexists. split.
    constructor. simpl. intro. reflexivity.
  + simpl. intros G0 q s0 h Hq IHq.
    decompose record IHq. eexists. split. constructor 2.
    exact H1. exact H2.
  (** mutual induction cases: cond *)
  + simpl. intros G0. eexists. eexists. 
    split. constructor. split. constructor.
    split; intros; reflexivity.
  + simpl. intros G0. eexists. eexists. 
    split. constructor. split. constructor.
    split; intros; reflexivity. 
  + simpl. intros G0 b t St Ht. eexists. eexists. 
    split. constructor. exact (sem_tm_bool_to_tribool Ht). split. constructor. exact (sem_tm_bool_to_tribool Ht).
    split; intros; destruct (St h); destruct b; reflexivity. 
  + simpl. intros G0 n p tml Stml e Html.
    cut (exists Sc2, SQLSem2.j_cond_sem d G0 (List.fold_right (fun (t : pretm) (acc : precond) => 
      (t IS NOT NULL) AND acc) (TRUE) tml) Sc2).
    intro Hc2. decompose record Hc2. clear Hc2. eexists. eexists.
    split. eapply (SQLSem2.jcs_pred _ _ _ _ _ _ e). Unshelve. 
    exact (sem_tml_bool_to_tribool Html).
    split. constructor. Unshelve. constructor. Unshelve. constructor. Unshelve. 
    exact (sem_tml_bool_to_tribool Html).
    exact H0. split.
    - intro. apply S3.sem_bpred_elim.
      * intros. apply S2.sem_bpred_elim; rewrite H1. 
        intros. injection H2; clear H2; intro H2. generalize dependent Hcl0. rewrite <- H2. intro.
        replace (p cl Hcl) with (p cl Hcl0).
        destruct (p cl Hcl0); reflexivity.
        f_equal. apply EqdepTheory.UIP.
        intro. discriminate H2.
      * intros. apply S2.sem_bpred_elim; rewrite H1.
        intros. discriminate H2.
        intro. reflexivity.
    - intro. erewrite <- (sem_bpred_tech _ _ _ _ _ _ _ _ (sem_tml_bool_to_tribool Html)). reflexivity. exact H0.
    - elim Html.
      * simpl. eexists. constructor.
      * intros t0 tml0 St0 Stml0 Ht0 Html0 IH. destruct IH. simpl. eexists. constructor.
        constructor. apply sem_tm_bool_to_tribool. exact Ht0. exact H0. 
  + hnf. intros G0 b tml q s0 Stml Sq e Html Hq IHq.
    decompose record IHq. destruct b.
    - cut (exists S2, SQLSem2.j_cond_sem d G0 (ffcond d (tml IN q)) S2).
      * intro Hff. decompose record Hff. clear Hff.
        eexists. exists x0. split. constructor. apply sem_tml_bool_to_tribool. exact Html. exact H1. split.
        exact H0. split.
        ++ intro h. simpl.        
          destruct (0 <? Rel.card (Rel.sel (Sq h)
           (fun rl : Rel.T (length s0) =>
            fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
            (length s0) rl (cast _ _ (f_equal Rel.T e) (Stml h))))) eqn:e0.
          -- transitivity true. reflexivity. symmetry. apply if_true.
            ** eapply (trans_eq _ e0). Unshelve. exact e. 
               rewrite (fold_v_tml_sem1' _ _ _ _ (sem_tml_bool_to_tribool Html) h).
               rewrite H2. reflexivity. apply cast_JMeq. reflexivity.
            ** reflexivity.
          -- transitivity false.
            ** destruct (0 <? Rel.card (Rel.sel (Sq h)
               (fun rl : Rel.T (length s0) => fold_right2 (fun (r0 V0 : Value) (acc : bool) => 
                 (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool) true (length s0) rl (cast _ _ (f_equal Rel.T e) (Stml h)))));
             reflexivity.
            ** symmetry. apply if_false.
              +++ rewrite <- e0. rewrite (fold_v_tml_sem1' _ _ _ _ (sem_tml_bool_to_tribool Html) h).
               rewrite H2. reflexivity. apply cast_JMeq. reflexivity.
              +++ apply if_elim; reflexivity.
        ++ intro. rewrite H2. simpl in H0. pose (s1 := freshlist (length tml)).
           cut (exists Sc, SQLSem2.j_cond_sem d (s1 :: G0)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s1)) Sc).
           intro Hcut. Focus 2. eapply tech_j_cond_fold'.
           symmetry. apply length_freshlist. apply p_freshlist. apply sem_tml_bool_to_tribool. exact Html. intro. intuition.
           decompose record Hcut. 
           assert (Rel.T (length s0) = Rel.T (list_sum (List.map (length (A:=Name)) (freshlist (length tml) :: Datatypes.nil)))).
             symmetry. rewrite <- length_concat_list_sum. simpl. rewrite app_length, length_freshlist.
             unfold Rel.T, Rel.V. rewrite <- e. unfold Rel.T, Rel.V. f_equal. simpl. omega.
           erewrite (cond_sem_not_ex_selstar' _ _ _ _ _ _ _ _ _ _ _ H0 H1 H3). Unshelve.
           Focus 2. exact H4.
           destruct (0 <? Rel.card (Rel.sel (x h) (fun rl : Rel.T (length s0) =>
             fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool)
             true (length s0) rl (cast (Rel.T (length tml)) (t Value (length s0)) (f_equal Rel.T e) (Stml h))))) eqn:e1.
          -- transitivity false.
             destruct (0 <? Rel.card (Rel.sel (x h) (fun rl : Rel.T (length s0) =>
               fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
               (length s0) rl (cast (Rel.T (length tml)) (t Value (length s0)) (f_equal Rel.T e) (Stml h))))) eqn:e2;
             generalize dependent e2; generalize dependent e1; simpl; unfold Rel.T, Rel.V; intros e1 e2; rewrite e1, e2; reflexivity.
             symmetry. transitivity (negb true); try reflexivity. 
             rewrite <- e1 at 1. f_equal. f_equal. apply eq_card_dep; auto.
             apply eq_sel; auto.
             ** intros. rewrite H5. reflexivity.
             ** intros. unfold S2.is_btrue.
                assert (exists (r1' : Rel.T (list_sum (List.map (length (A:=Name)) (freshlist (length tml) :: List.nil)))), r1' ~= r1). rewrite <- H4; eauto.
                destruct H6. transitivity (x1 (Ev.env_app _ _ (Ev.env_of_tuple _ x2) h)).
                f_equal. f_equal. f_equal. apply JMeq_eq. apply cast_JMeq. symmetry. exact H6.
                erewrite (tech_sem_not_exists' _ _ _ _ _ _ _ Stml).
                Focus 3. symmetry. eapply (cast_JMeq _ _ _ _ _ _ (JMeq_sym H6)).
                Focus 2. apply length_freshlist. apply JMeq_eq.
                eapply (f_JMequal (fold_right2 _ _ _ _) (fold_right2 _ _ _ _)).
                eapply (f_JMequal (fold_right2 _ _ _) (fold_right2 _ _ _)).
                rewrite e. reflexivity.
                apply cast_JMeq. exact H5.
                symmetry. apply cast_JMeq. reflexivity.
                exact H3. apply sem_tml_bool_to_tribool. exact Html. Unshelve.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
          -- transitivity true.
             ** unfold Rel.T, Rel.V in e1. unfold Rel.T, Rel.V. rewrite e1. apply if_false; auto.
                generalize e1; clear e1. apply bool_contrapos.
                intro. apply Nat.ltb_lt in H5. apply Nat.ltb_lt.
                apply (lt_le_trans _ _ _ H5). apply le_card_eq_not_neq.
             ** symmetry. transitivity (negb false); try reflexivity. f_equal.
                rewrite <- e1. f_equal. apply eq_card_dep; auto.
                apply eq_sel; auto.
                +++ intros. rewrite H5. reflexivity.
                +++ intros. 
                    assert (exists r1' : Rel.T (length tml), r1 ~= r1').
                    rewrite e. eexists. reflexivity. destruct H6.
                    erewrite tech_sem_not_exists'. Focus 3. apply cast_JMeq. exact H6.
                    Focus 2. apply length_freshlist.
                    apply JMeq_eq.
                    eapply (f_JMequal (fold_right2 _ _ _ _) (fold_right2 _ _ _ _)).
                    eapply (f_JMequal (fold_right2 _ _ _ ) (fold_right2 _ _ _ )).
                    rewrite e. reflexivity.
                    symmetry. rewrite <- H5. exact H6.
                    symmetry. apply cast_JMeq. reflexivity.
                    exact H3. apply sem_tml_bool_to_tribool. exact Html. Unshelve.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
          -- symmetry. rewrite e. apply length_freshlist.
      * destruct (tech_j_cond_fold' d (freshlist (length tml)) (freshlist (length tml)) G0 _ 
            (eq_sym (length_freshlist _)) (p_freshlist _) _ (sem_tml_bool_to_tribool Html) (fun x Hx => Hx)).
        eexists. constructor. constructor. constructor. constructor. constructor. constructor. exact H1.
        constructor. rewrite length_freshlist. symmetry. exact e. constructor. exact H0.
        Unshelve. simpl. repeat rewrite plus_0_r. rewrite length_freshlist. rewrite e. reflexivity.
        simpl. rewrite length_freshlist, e. reflexivity.
    - cut (exists S1, SQLSem2.j_cond_sem d G0 (ttcond d (tml NOT IN q)) S1).
      * intro Htt. decompose record Htt. clear Htt. exists x0.
        eexists. split. exact H0. split. constructor. apply sem_tml_bool_to_tribool. exact Html. exact H1. split.
        ++ intro. rewrite H2. simpl in H0. pose (s1 := freshlist (length tml)).
           cut (exists Sc, SQLSem2.j_cond_sem d (s1 :: G0)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s1)) Sc).
           intro Hcut. Focus 2. eapply tech_j_cond_fold'.
           symmetry. apply length_freshlist. apply p_freshlist. apply sem_tml_bool_to_tribool. exact Html. intro. intuition.
           decompose record Hcut. 
           assert (Rel.T (length s0) = Rel.T (list_sum (List.map (length (A:=Name)) (freshlist (length tml) :: Datatypes.nil)))).
             symmetry. rewrite <- length_concat_list_sum. simpl. rewrite app_length, length_freshlist.
             unfold Rel.T, Rel.V. rewrite <- e. unfold Rel.T, Rel.V. f_equal. simpl. omega.
           erewrite (cond_sem_not_ex_selstar' _ _ _ _ _ _ _ _ _ _ _ H0 H1 H3). Unshelve.
           Focus 2. exact e. Focus 2. exact H4.
           destruct (0 <? Rel.card (Rel.sel (x h) (fun rl : Rel.T (length s0) =>
             fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool)
             true (length s0) rl (cast (Rel.T (length tml)) (t Value (length s0)) (f_equal Rel.T e) (Stml h))))) eqn:e1.
          -- transitivity false.
             destruct (0 <? Rel.card (Rel.sel (x h) (fun rl : Rel.T (length s0) =>
               fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
               (length s0) rl (cast (Rel.T (length tml)) (t Value (length s0)) (f_equal Rel.T e) (Stml h))))) eqn:e2;
             generalize dependent e2; generalize dependent e1; simpl; unfold Rel.T, Rel.V; intros e1 e2; rewrite e1, e2; reflexivity.
             symmetry. transitivity (negb true); try reflexivity. 
             rewrite <- e1 at 1. f_equal. f_equal. apply eq_card_dep; auto.
             apply eq_sel; auto.
             ** intros. rewrite H5. reflexivity.
             ** intros. unfold S2.is_btrue.
                assert (exists (r1' : Rel.T (list_sum (List.map (length (A:=Name)) (freshlist (length tml) :: List.nil)))), r1' ~= r1). rewrite <- H4; eauto.
                destruct H6. transitivity (x1 (Ev.env_app _ _ (Ev.env_of_tuple _ x2) h)).
                f_equal. f_equal. f_equal. apply JMeq_eq. apply cast_JMeq. symmetry. exact H6.
                erewrite (tech_sem_not_exists' _ _ _ _ _ _ _ Stml).
                Focus 3. symmetry. eapply (cast_JMeq _ _ _ _ _ _ (JMeq_sym H6)).
                Focus 2. apply length_freshlist. apply JMeq_eq.
                eapply (f_JMequal (fold_right2 _ _ _ _) (fold_right2 _ _ _ _)).
                eapply (f_JMequal (fold_right2 _ _ _) (fold_right2 _ _ _)).
                rewrite e. reflexivity.
                apply cast_JMeq. exact H5.
                symmetry. apply cast_JMeq. reflexivity.
                exact H3. apply sem_tml_bool_to_tribool. exact Html. Unshelve.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
                rewrite e; reflexivity.
          -- transitivity true.
             ** unfold Rel.T, Rel.V in e1. unfold Rel.T, Rel.V. rewrite e1. apply if_false; auto.
                generalize e1; clear e1. apply bool_contrapos.
                intro. apply Nat.ltb_lt in H5. apply Nat.ltb_lt.
                apply (lt_le_trans _ _ _ H5). apply le_card_eq_not_neq.
             ** symmetry. transitivity (negb false); try reflexivity. f_equal.
                rewrite <- e1. f_equal. apply eq_card_dep; auto.
                apply eq_sel; auto.
                +++ intros. rewrite H5. reflexivity.
                +++ intros. 
                    assert (exists r1' : Rel.T (length tml), r1 ~= r1').
                    rewrite e. eexists. reflexivity. destruct H6.
                    erewrite tech_sem_not_exists'. Focus 3. apply cast_JMeq. exact H6.
                    Focus 2. apply length_freshlist.
                    apply JMeq_eq.
                    eapply (f_JMequal (fold_right2 _ _ _ _) (fold_right2 _ _ _ _)).
                    eapply (f_JMequal (fold_right2 _ _ _ ) (fold_right2 _ _ _ )).
                    rewrite e. reflexivity.
                    symmetry. rewrite <- H5. exact H6.
                    symmetry. apply cast_JMeq. reflexivity.
                    exact H3. apply sem_tml_bool_to_tribool. exact Html. Unshelve.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
          -- symmetry. rewrite e. apply length_freshlist.
        ++ intro h. simpl.
          destruct (0 <? Rel.card (Rel.sel (Sq h)
           (fun rl : Rel.T (length s0) =>
            fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
            (length s0) rl (cast _ _ (f_equal Rel.T e) (Stml h))))) eqn:e0.
          -- transitivity true. reflexivity. symmetry. apply if_true.
            ** rewrite <- e0 at 1. rewrite (fold_v_tml_sem1' _ _ _ _ (sem_tml_bool_to_tribool Html) h). rewrite H2. reflexivity.
               apply cast_JMeq. reflexivity.
            ** reflexivity.
          -- transitivity false.
            ** destruct (0 <? Rel.card (Rel.sel (Sq h)
               (fun rl : Rel.T (length s0) => fold_right2 (fun (r0 V0 : Value) (acc : bool) => 
                 (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool) true (length s0) rl (cast _ _ (f_equal Rel.T e) (Stml h)))));
             reflexivity.
            ** symmetry. apply if_false.
              +++ rewrite <- e0. rewrite (fold_v_tml_sem1' _ _ _ _ (sem_tml_bool_to_tribool Html) h). 
                  decompose record IHq. destruct (SQLSem2.jq_sem_fun_dep _ _ _ _ _ H4 _ _ _ _ eq_refl eq_refl H1).
                  rewrite H6 in H5. rewrite H5. reflexivity.
                  apply cast_JMeq. reflexivity.
              +++ apply if_elim; reflexivity.
      * destruct (tech_j_cond_fold' d (freshlist (length tml)) (freshlist (length tml)) G0 _ 
            (eq_sym (length_freshlist _)) (p_freshlist _) _ (sem_tml_bool_to_tribool Html) (fun x Hx => Hx)).
        eexists. constructor. constructor. constructor. constructor. constructor. constructor. exact H1.
        constructor. rewrite length_freshlist. symmetry. exact e. constructor. exact H0.
        Unshelve. simpl. repeat rewrite plus_0_r. rewrite length_freshlist. rewrite e. reflexivity.
        simpl. rewrite length_freshlist, e. reflexivity.
  + simpl. intros G0 q Sq Hq IHq. decompose record IHq.
    eexists. eexists. 
    split. constructor. exact H1. split. constructor. constructor. exact H1.
    split; intro; rewrite H2; destruct (x h); reflexivity.
  + simpl. intros G0 c1 c2 Sc1 Sc2 Hc1 IHc1 Hc2 IHc2.
    decompose record IHc1. decompose record IHc2. eexists. eexists.
    split. constructor. exact H0. exact H3.
    split. constructor. exact H1. exact H5.
    split.
    - intro. rewrite S3_is_btrue_and. rewrite S2_is_btrue_and.
      rewrite H2, H6. reflexivity.
    - intro. rewrite negtb_andtb. rewrite S3_is_btrue_or. rewrite S2_is_btrue_or.
      rewrite H4, H8. reflexivity.
  + simpl. intros G0 c1 c2 Sc1 Sc2 Hc1 IHc1 Hc2 IHc2.
    decompose record IHc1. decompose record IHc2. eexists. eexists.
    split. constructor. exact H0. exact H3.
    split. constructor. exact H1. exact H5.
    split.
    - intro. rewrite S3_is_btrue_or. rewrite S2_is_btrue_or.
      rewrite H2, H6. reflexivity.
    - intro. rewrite negtb_ortb. rewrite S3_is_btrue_and. rewrite S2_is_btrue_and.
      rewrite H4, H8. reflexivity.
  + simpl. intros G0 c0 Sc0 Hc0 IHc0. decompose record IHc0.
    eexists. eexists. 
    split. exact H1. split. exact H0. 
    split. exact H4. intro. rewrite negtb_negtb. apply H2.
  (** mutual induction cases: btb *)
  + simpl. intros G0. eexists. split. constructor.
    intro. reflexivity.
  + simpl. intros G0 T s' btb s0 G1 ST Sbtb e HT IHT Hbtb IHbtb e'.
    decompose record IHT. decompose record IHbtb.
    eexists. split. constructor. exact H1. exact H3. exact e'.
    intro. apply cast_JMeq. symmetry. apply cast_JMeq.
    rewrite H2, H4. reflexivity.
  (** mutual induction cases: btbl *)
  + simpl. intros G0. eexists. split. constructor.
    intro. reflexivity.
  + simpl. intros G0 btb btbl G1 G2 Sbtb Sbtbl e Hbtb IHbtb Hbtbl IHbtbl.
    decompose record IHbtb. decompose record IHbtbl. clear IHbtb IHbtbl.
    eexists. split. constructor. exact H1. exact H3.
    intro; simpl. Unshelve.
    2: { rewrite e'; reflexivity. }
    2: { rewrite <- length_concat_list_sum, map_app, length_concat_list_sum, list_sum_app. reflexivity. }
    rewrite H2. apply (f_JMeq _ _ (Rel.rsum (x h))).
    extensionality Vl. apply JMeq_eq. apply cast_JMeq. symmetry. apply cast_JMeq.
    rewrite H4. reflexivity.
  (** mutual induction cases: inquery *)
  + simpl. intros G0 b tml btbl c G1 Sbtbl Sc Stml Hbtbl IHbtbl Hc IHc Html.
    decompose record IHbtbl. decompose record IHc.
    eexists. split. eapply (SQLSem2.jiqs_sel _ _ _ _ _ _ _ _ _ _ H1 H0 (sem_tml_bool_to_tribool Html)).
    intro. simpl. destruct b.
    - apply eq_JMeq. f_equal. f_equal. f_equal. apply JMeq_eq. rewrite H2.
      eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMeq _ _ (@Rel.sum _ _)). apply JMeq_eq. eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
      reflexivity. reflexivity. reflexivity.
    - apply eq_JMeq. f_equal. f_equal. apply JMeq_eq. rewrite H2.
      eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMeq _ _ (@Rel.sum _ _)). apply JMeq_eq. eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity. reflexivity. reflexivity. reflexivity.
  + simpl. intros G0 b btb c G1 Sbtb Sc Hbtb IHbtb Hc IHc.
    decompose record IHbtb. decompose record IHc.
    eexists. split. eapply (SQLSem2.jiqs_selstar _ _ _ _ _ _ _ _ H1 H0).
    intro. simpl. destruct b.
    - apply eq_JMeq. f_equal. f_equal. rewrite H2. apply JMeq_eq.
      eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
    - apply eq_JMeq. f_equal. f_equal. rewrite H2. apply JMeq_eq.
      eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
  + simpl. intros G0 b q1 q2 s0 S1 S2 Hq1 IHq1 Hq2 IHq2.
    decompose record IHq1. decompose record IHq2.
    eexists. split. eapply (SQLSem2.jiqs_union _ _ _ _ _ _ _ _ H1 H3).
    intro. rewrite H2, H4. reflexivity.
  + simpl. intros G0 b q1 q2 s0 S1 S2 Hq1 IHq1 Hq2 IHq2.
    decompose record IHq1. decompose record IHq2.
    eexists. split. eapply (SQLSem2.jiqs_inters _ _ _ _ _ _ _ _ H1 H3).
    intro. rewrite H2, H4. reflexivity.
  + simpl. intros G0 b q1 q2 s0 S1 S2 Hq1 IHq1 Hq2 IHq2.
    decompose record IHq1. decompose record IHq2.
    eexists. split. eapply (SQLSem2.jiqs_except _ _ _ _ _ _ _ _ H1 H3).
    intro. rewrite H2, H4. reflexivity.
  Qed.

End Translation2V.