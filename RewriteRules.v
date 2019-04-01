Require Import Eqdep Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool 
  Semantics JMeq FunctionalExtensionality Omega Coq.Init.Specif ProofIrrelevance Util RelFacts SemFacts.

Module RewriteRules (Db : DB) (Sql : SQL Db).
  Import Db.
  Import Sql.

  Module RF := RelFacts.Facts Db Sql.
  Module SF := SemFacts.Facts Db Sql.
  Import RF.
  Import SF.

  Module S2 := Sem2 Db.
  Module S3 := Sem3 Db.
  Module Ev := Evl Db Sql.
  Module SQLSem2 := SQLSemantics Db S2 Sql Ev.
  Module SQLSem3 := SQLSemantics Db S3 Sql Ev.

  Definition tml_of_scm s n := List.map (fun a => tmvar (n,a)) s.
  Definition btm_of_tml (tml : list pretm) (al : list Name) := List.combine tml al.
  Definition btm_of_scm s al n := btm_of_tml (tml_of_scm s n) al.

(*
  Derive Inversion j_nil_btb_sem with (forall d G G' Snil, SQLSem3.j_btb_sem d G G' List.nil Snil) Sort Prop.

  not the inversion I'd expect, so I'll use a customized version

  Lemma j_nil_btb_sem :
    forall d G G' Snil (P : Prop),
       (forall (G0 G0': Ctx), G0 = G -> G0' = G' -> List.nil = G0' ->
        (fun (_:Ev.env G) => Rel.Rone) ~= Snil -> P) ->
       SQLSem3.j_btb_sem d G G' List.nil Snil -> P.
  Proof.
    intros.
    enough (forall G0 G0' (btb0 : list (pretb * Scm)) 
      (Snil0 : Ev.env G0 -> Rel.R (list_sum (List.map (length (A:=Name)) G0'))), 
        SQLSem3.j_btb_sem d G0 G0' btb0 Snil0 ->
        G0 = G -> G0' = G' -> List.nil = btb0 -> Snil0 ~= Snil -> P).
    apply (H1 _ _ _ _ H0 eq_refl eq_refl eq_refl JMeq_refl).
    intros G0 G0' btb0 Snil0 H0'.
    destruct H0'; intros. eapply H; auto. rewrite H1 in H4. exact H4.
    discriminate H5.
  Qed.

*)

  Lemma j_commutative_join_btb d G T1 T2 s1 s2 Ga Gb S1 S2 h :
    forall ra rb (r1 : Rel.T (length s1)) (r2 : Rel.T (length s2)), 
    ra ~= Vector.append r1 r2 -> rb ~= Vector.append r2 r1 ->
    SQLSem3.j_btb_sem d G Ga ((T1,s1)::(T2,s2)::List.nil) S1 ->
    SQLSem3.j_btb_sem d G Gb ((T2,s2)::(T1,s1)::List.nil) S2 ->
      Rel.memb (S1 h) ra = Rel.memb (S2 h) rb.
  Proof.
    intros.
    (* some case analysis (inversion) *)
    eapply (SQLSem3.j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H1). Unshelve.
      clear H1; intros; subst. apply (existT_eq_elim H12); clear H11 H12; intros; subst. 
      apply (existT_eq_elim (JMeq_eq H4)); clear H4 H3; intros; subst.
    clear H3. eapply (SQLSem3.j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H8). Unshelve.
      clear H8; intros; subst. apply (existT_eq_elim H15); clear H15 H14; intros; subst.
      apply (existT_eq_elim (JMeq_eq H10)); clear H7 H10; intros; subst.
    clear H7. inversion H8. eapply (SQLSem3.j_nil_btb_sem _ _ _ _ _ _ H8). Unshelve.
      clear H8; intros. subst. clear H11 H13.
    eapply (SQLSem3.j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H2). Unshelve.
      clear H2; intros; subst. apply (existT_eq_elim H18); clear H17 H18; intros; subst.
      apply (existT_eq_elim (JMeq_eq H12)); clear H11 H12; intros; subst.
    clear H11. eapply (SQLSem3.j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H8). Unshelve.
      clear H8; intros; subst. apply (existT_eq_elim H20); clear H19 H20; intros; subst.
      apply (existT_eq_elim (JMeq_eq H15)); clear H14 H15; intros; subst.
    clear H14. eapply (SQLSem3.j_nil_btb_sem _ _ _ _ _ _ H12). Unshelve.
      clear H12; intros; subst.
    eapply (cast_elim (Rel.T (length s0)) r1). rewrite H9. reflexivity. intros r1' Hr1'.
    eapply (cast_elim (Rel.T (length s3)) r2). rewrite H5. reflexivity. intros r2' Hr2'.
    (* proof *)
    transitivity (Rel.memb (Rel.times (ST h) (ST0 h)) (append r1' r2')).
    + apply eq_memb_dep. rewrite H5, H9. simpl. omega.
      apply cast_JMeq. apply eq_times_dep; auto. rewrite H5. simpl. omega.
      apply cast_JMeq. apply p_ext_dep.
        simpl. omega. 
        intros. replace r0 with (append r3 (Vector.nil _)).
        rewrite (Rel.p_times _ _ _ _ _ _ _ eq_refl). rewrite Rel.p_one. omega.
        apply JMeq_eq. apply (JMeq_trans (vector_append_nil_r _)). symmetry. exact H12.
        apply (JMeq_trans H). eapply (f_JMequal (append _) (append _)). Unshelve.
        eapply (f_JMequal append append). Unshelve.
        - rewrite H5, H9. reflexivity.
        - exact Hr1'.
        - exact Hr2'.
        - rewrite H5. reflexivity.
        - rewrite H5, H9. reflexivity.
        - rewrite H9. reflexivity.
        - rewrite H5, H9. reflexivity.
    + eapply (cast_elim (Rel.T (length s5)) r1'). rewrite H9, H13. reflexivity. intros r1'' Hr1''.
      eapply (cast_elim (Rel.T (length s4)) r2'). rewrite H5, H10. reflexivity. intros r2'' Hr2''.
      destruct (SQLSem3.jT_sem_fun_dep _ _ _ _ _ H4 _ _ _ _ eq_refl eq_refl H7).
      destruct (SQLSem3.jT_sem_fun_dep _ _ _ _ _ H6 _ _ _ _ eq_refl eq_refl H11).
      transitivity (Rel.memb (Rel.times (ST1 h) (ST2 h)) (append r2'' r1'')).
      - rewrite (Rel.p_times _ _ _ _ _ _ _ eq_refl). rewrite (Rel.p_times _ _ _ _ _ _ _ eq_refl).
        rewrite mult_comm. f_equal. 
        apply eq_memb_dep; intuition. eapply (f_JMequal ST0 ST1). Unshelve. exact H14. reflexivity.
        apply eq_memb_dep; intuition. eapply (f_JMequal ST ST2). Unshelve. exact H17. reflexivity.
        reflexivity. rewrite H5, H10. reflexivity. reflexivity. rewrite H9, H13. reflexivity.
      - apply eq_memb_dep. 
        simpl. rewrite plus_0_r. rewrite H10, H13. reflexivity.
        symmetry. apply cast_JMeq. apply eq_times_dep; auto.
        simpl. rewrite H13. omega.
        apply cast_JMeq. rewrite <- H16.
        apply p_ext_dep. simpl. omega.
        intros. replace r0 with (append r3 (Vector.nil _)). 
        rewrite (Rel.p_times _ _ _ _ _ _ _ eq_refl). rewrite Rel.p_one. omega.
        apply JMeq_eq. apply (JMeq_trans (vector_append_nil_r _)). symmetry. exact H18.
        symmetry. apply (JMeq_trans H0). eapply (f_JMequal (append _) (append _)). Unshelve.
        eapply (f_JMequal append append). Unshelve.
        * rewrite H10, H13. reflexivity.
        * apply (JMeq_trans Hr2' Hr2'').
        * apply (JMeq_trans Hr1' Hr1'').
        * rewrite H13. reflexivity.
        * rewrite H10, H13. reflexivity.
        * rewrite H10. reflexivity.
        * rewrite H10, H13. reflexivity.
  Qed.

  Fixpoint tmlist_of_ctx_i (G: Ctx) : nat -> list pretm := 
    fun i => match G with
    | List.nil => List.nil
    | s::G0 => List.map (fun x => tmvar (i,x)) s ++ tmlist_of_ctx_i G0 (S i)
    end.

  Lemma tmlist_of_ctx_O G : tmlist_of_ctx G = tmlist_of_ctx_i G 0.
  Proof.
    unfold tmlist_of_ctx, mapi. generalize 0. induction G; simpl; intuition.
    f_equal. apply IHG.
  Qed.

  Derive Inversion j_nil_sem with (forall G Snil, Ev.j_tml_sem0 G List.nil Snil) Sort Prop.
  Derive Inversion j_cons_sem with (forall G hd tl Scons, Ev.j_tml_sem0 G (hd::tl) Scons) Sort Prop.

  Derive Inversion j_tmvar_sem with (forall G n a Svar, Ev.j_tm_sem0 G (tmvar (n,a)) Svar) Sort Prop.
  Derive Inversion jfv_O_sem with (forall s G a Svar, Ev.j_fvar_sem (s::G) O a Svar) Sort Prop.
  Derive Inversion jfv_S_sem with (forall s G i a Svar, Ev.j_fvar_sem (s::G) (S i) a Svar) Sort Prop.

  Lemma j_var_sem_tech : forall a s1 s2 (x : Rel.T (S (length s2))) (y : Rel.T (length s1)) e,
    forall Sa,
    Ev.j_var_sem (s1 ++ a :: s2) a Sa ->
    Sa (Ev.env_of_tuple ((s1++a::s2)::List.nil) (cast _ _ e (Vector.append y x))) ~= hd x.
  Proof.
    intros a s1. induction s1; simpl; intuition.
    + inversion H.
      - rewrite <- (existT_projT2_eq _ _ _ H4). clear H4. subst.
        apply eq_JMeq. apply env_hd_hd.
        rewrite (projT1_env_app ((a::s2)::List.nil) List.nil). simpl.
        rewrite app_nil_r. replace y with (Vector.nil Rel.V). simpl.
        apply (split_ind (@tl Rel.V
                ((fix add (n m : nat) {struct n} : nat := match n with
                                                          | 0 => m
                                                          | S p => S (add p m)
                                                          end) (@length Name s2) 0)
                (cast (t Rel.V (S (@length Name s2))) (Rel.T (S (@length Name s2 + 0))) e x))).
        simpl; intros. f_equal. apply JMeq_eq. eapply (f_JMequal hd hd). Unshelve.
        rewrite plus_0_r. reflexivity. 
        apply cast_JMeq. reflexivity. 
        eapply (case0 (fun v => nil _ = v)). reflexivity.
        rewrite plus_0_r. reflexivity.
        rewrite plus_0_r. reflexivity.
      - contradiction H4. reflexivity.
    + inversion H.
      - contradiction H3. apply in_or_app. right. left. reflexivity.
      - rewrite <- (existT_projT2_eq _ _ _ H2). clear H2. subst.
        eapply (JMeq_trans _ (IHs1 _ _ (tl y) _ _ H5)). Unshelve.
        Focus 2. simpl. rewrite plus_0_r. rewrite app_length. reflexivity.
        apply eq_JMeq. f_equal. apply Ev.env_eq.
        rewrite env_tl_tl. rewrite (projT1_env_app ((a0::s1++a::s2)::List.nil) List.nil).
        rewrite projT1_env_of_tuple. simpl.
        apply (split_ind (@tl Rel.V
                ((fix add (n m : nat) {struct n} : nat := match n with
                                                          | 0 => m
                                                          | S p => S (add p m)
                                                          end) (@length Name (s1 ++ a :: s2)) 0)
                (cast (t Rel.V (S (@length Name s1 + S (@length Name s2))))
                   (Rel.T (S (@length Name (s1 ++ a :: s2) + 0))) e
                   (@append Rel.V (S (@length Name s1)) (S (@length Name s2)) y x)))).
        simpl; intros. transitivity (to_list v1). rewrite app_nil_r. reflexivity.
        apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
        * rewrite plus_0_r. reflexivity.
        * symmetry. apply cast_JMeq. rewrite <- tl_append.
          eapply (@JMeq_trans _ _ _ _ (append v1 v2)).
          eapply (JMeq_trans _ (eq_JMeq H0)). Unshelve.
          replace v2 with (nil Rel.V). apply vector_append_nil_r.
          eapply (case0 (fun v => nil Rel.V = v)). reflexivity.
          eapply (f_JMequal tl tl). Unshelve.
          rewrite plus_0_r. rewrite app_length. reflexivity.
          symmetry. apply cast_JMeq. reflexivity.
          rewrite plus_0_r. rewrite app_length. reflexivity.
          rewrite plus_0_r. rewrite app_length. reflexivity.
        * rewrite plus_0_r. reflexivity.
        * rewrite plus_0_r. reflexivity.
  Qed.

  Lemma j_tm_sem_env_app_subind a s1 s2 G1 G2 : 
    forall Stm,
    Ev.j_tm_sem (G1 ++ (s1 ++ a :: s2) :: G2) (tmvar (length G1, a)) Stm ->
    forall (x : Rel.T (S (length s2))) (y : Rel.T (length s1)) e,
    forall h1 h2, Stm (Ev.env_app _ _ h1 (Ev.env_app ((s1++a::s2)::List.nil) G2 
        (Ev.env_of_tuple ((s1++a::s2)::List.nil) (cast _ _ e (Vector.append y x))) h2)) 
        ~= hd x.
  Proof.
    intros Stm H. eapply (j_tmvar_sem _ _ _ _ (fun G0 n0 a0 Svar0 => _) _ H). Unshelve.
    simpl; intros; subst. clear H H0.
    induction G1; simpl; intros.
    + simpl in H3. eapply (jfv_O_sem _ _ _ _ (fun s0 G0 a0 Svar0 => _) _ H3). Unshelve.
      simpl; intros; subst.
      rewrite <- (existT_projT2_eq _ _ _ H5); clear H5. rewrite env_app_nil_l. rewrite subenv1_app.
      eapply (JMeq_trans _ (j_var_sem_tech _ _ _ x y _ _ H4)). Unshelve. Focus 2.
      simpl. rewrite app_length. rewrite plus_0_r. reflexivity.
      apply eq_JMeq. f_equal. apply Ev.env_eq. simpl.
      f_equal. f_equal. f_equal. f_equal.
      apply JMeq_eq. apply cast_JMeq. symmetry. apply cast_JMeq. reflexivity.
    + simpl in H3. eapply (jfv_S_sem _ _ _ _ _ (fun s0 G0 i0 a0 Svar0 => _) _ H3). Unshelve.
      simpl; intros; subst. rewrite <- (existT_projT2_eq _ _ _ H6); clear H6.
      eapply (JMeq_trans _ (IHG1 _ H4 (@Ev.subenv2 (a0::List.nil) G1 h1))). Unshelve.
      apply eq_JMeq. f_equal. apply Ev.env_eq. simpl.
      erewrite skipn_app_l.
      - reflexivity.
      - destruct h1. simpl. rewrite <- (proj1 (Nat.eqb_eq _ _) e0).
        simpl. repeat rewrite app_length. simpl. omega.
  Qed.

  Lemma j_tml_sem_env_app_subind s2 G1 G2 : 
    forall s1 Stml,
    Ev.j_tml_sem (G1 ++ (s1 ++ s2) :: G2) (List.map (fun x1 => tmvar (length G1, x1)) s2) Stml ->
    forall (x : Rel.T (length s2)) (y : Rel.T (length s1)) e,
    forall h1 h2, Stml (Ev.env_app _ _ h1 (Ev.env_app ((s1++s2)::List.nil) G2 
        (Ev.env_of_tuple ((s1++s2)::List.nil) (cast _ _ e (Vector.append y x))) h2)) 
        ~= x.
  Proof.
    induction s2; simpl; intuition.
    + eapply (case0 (fun v => v ~= x) _ _). Unshelve. simpl.
      eapply (case0 (fun v => nil Rel.V ~= v) _ x). Unshelve. reflexivity.
    + simpl. eapply (j_cons_sem _ _ _ _ (fun G0 hd tl Stml0 => _) _ H). Unshelve.
      intros. simpl. rewrite <- (existT_projT2_eq _ _ _ H5).
      eapply (@JMeq_trans _ _ _ _ (Vector.cons _ (hd x) _ (tl x))).
      - apply cons_equal.
        * apply JMeq_eq. eapply (JMeq_trans _ (j_tm_sem_env_app_subind _ _ _ _ _ _ H2 x y _ h1 h2)). Unshelve.
          Focus 2. simpl. rewrite plus_0_r. rewrite app_length. reflexivity.
          apply eq_JMeq. f_equal. apply Ev.env_eq.
          repeat rewrite projT1_env_app. f_equal.
          rewrite (projT1_env_app ((s1 ++ a :: s2) :: List.nil) G2). f_equal.
          rewrite (projT1_env_app ((s1++a::s2)::List.nil) List.nil). simpl. f_equal. f_equal. f_equal. f_equal.
          apply JMeq_eq. apply cast_JMeq. symmetry. apply cast_JMeq. reflexivity.
        * apply map_length.
        * assert (exists Stml0' 
            (H4': Ev.j_tml_sem0 (G1 ++ ((s1++(a::List.nil))++s2)::G2) (List.map (fun x1 => tmvar (length G1,x1)) s2) Stml0'),
            Stml0 ~= Stml0' /\ H4 ~= H4').
          rewrite <- app_assoc. exists Stml0. exists H4. intuition.
          destruct H6. destruct H6. destruct H6.
          eapply (JMeq_trans _ (IHs2 (s1++(a::List.nil)) x0 x1 (tl x) _ _ h1 h2)). Unshelve.
          Focus 2. rewrite app_length. apply (Vector.append y (of_list (hd x::List.nil))).
          Focus 2. unfold Rel.T. f_equal. simpl. repeat rewrite app_length. omega.
          eapply (f_JMequal Stml0 x0). exact H6. apply Ev.env_JMeq.
          ++ rewrite <- app_assoc. reflexivity.
          ++ repeat rewrite projT1_env_app. f_equal.
            rewrite (projT1_env_app ((s1 ++ a::s2)::List.nil) G2). f_equal.
            rewrite projT1_env_of_tuple. simpl. rewrite app_nil_r.
            apply JMeq_eq. eapply (f_JMequal (@to_list Rel.V _) (@to_list Rel.V _)). Unshelve.
            -- eapply (f_JMeq _ _ (@to_list Rel.V)). repeat rewrite app_length. simpl. omega.
            -- symmetry. apply cast_JMeq. 
               apply (split_ind (cast (Vector.t Rel.V (length s1 + S (length s2))) (Rel.T (length (s1 ++ a :: s2) + 0)) e (append y x))).
               intros. simpl. enough (v2 = Vector.nil _). enough (append y x ~= v1).
              ** apply eq_vector_to_list. repeat rewrite app_length; simpl; omega.
                transitivity (to_list (append (append y (cons _ (hd x) 0 (nil _))) (tl x))).
                apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
                repeat rewrite app_length. reflexivity.
                eapply (f_JMequal (append _) (append _)). Unshelve.
                eapply (f_JMequal append append). Unshelve. repeat rewrite app_length. reflexivity.
                rewrite (app_length s1 (a::Datatypes.nil)). reflexivity.
                reflexivity. apply JMeq_eq.
                eapply (@JMeq_trans _ _ _ _ (to_list (append y x))).
                repeat rewrite to_list_append. rewrite <- app_assoc. eapply (f_JMeq _ _ (app (to_list y))).
                transitivity (to_list (cons _ (hd x) _ (tl x))).
                reflexivity. rewrite (Vector.eta x) at 3. reflexivity.
                eapply (f_JMequal to_list to_list). Unshelve. repeat rewrite app_length. reflexivity. exact H10.
                repeat rewrite app_length. reflexivity.
                repeat rewrite app_length. reflexivity.
                reflexivity.
                repeat rewrite app_length. reflexivity.
                rewrite app_length. reflexivity.
                repeat rewrite app_length. reflexivity.
                rewrite app_length. reflexivity.
                rewrite app_length. reflexivity.
              ** rewrite H9 in H8.
                eapply (@JMeq_trans _ _ _ _ (append v1 (nil _))).
                eapply (JMeq_trans _ (eq_JMeq H8)).
                apply vector_append_nil_r. Unshelve.
                symmetry. apply cast_JMeq. reflexivity.
              ** eapply (case0 (fun v0 => v0 = nil Rel.V)). reflexivity.
            -- f_equal. rewrite <- app_assoc. reflexivity.
            -- rewrite <- app_assoc. reflexivity.
            -- f_equal. repeat rewrite app_length. simpl. omega.
            -- repeat rewrite app_length. simpl. rewrite plus_0_r. rewrite <- plus_assoc. reflexivity.
      - rewrite <- Vector.eta. reflexivity.
  Qed.

  Lemma j_tml_sem_env_app s G1 G2 :
    forall Stml,
    Ev.j_tml_sem (G1 ++ s :: G2) (List.map (fun x1 => tmvar (length G1, x1)) s) Stml ->
    forall (x : Rel.T (length s)) e,
    forall h1 h2, Stml (Ev.env_app _ _ h1 (Ev.env_app (s::List.nil) G2 
        (Ev.env_of_tuple (s::List.nil) (cast _ _ e x)) h2))
        ~= x.
  Proof.
    intros. apply (j_tml_sem_env_app_subind s G1 G2 List.nil Stml H x (Vector.nil _) e h1 h2).
  Qed.

  Lemma j_tml_sem_app G tml1 tml2 :
    forall S, Ev.j_tml_sem G (tml1 ++ tml2) S ->
    exists S1 S2, Ev.j_tml_sem G tml1 S1 /\ Ev.j_tml_sem G tml2 S2 /\ forall h, S h ~= append (S1 h) (S2 h).
  Proof.
    induction tml1; simpl; intuition.
    + exists (fun _ => Vector.nil _). exists S. intuition. constructor.
    + eapply (j_cons_sem _ _ _ _ (fun G0 hd tl Stml0 => _) _ H). Unshelve.
      intros; simpl; subst. destruct (IHtml1 _ H4). destruct H1. destruct H1. destruct H3.
      eexists. exists x0. intuition.
      - constructor. exact H2. exact H1.
      - rewrite <- (existT_projT2_eq _ _ _ H5). simpl. 
        eapply (f_JMequal (cons _ _ _) (cons _ _ _)); auto. Unshelve.
        rewrite app_length. reflexivity.
        rewrite app_length. reflexivity.
        rewrite app_length. reflexivity.
  Qed.

  Lemma length_tmlist_of_ctx_i G : forall i, length (tmlist_of_ctx_i G i) = length (concat G).
  Proof.
    induction G; simpl; intuition.
    do 2 rewrite app_length. rewrite map_length. auto.
  Qed.

  Lemma j_tml_sem_flip s1 s2 G :
    forall Stml,
    Ev.j_tml_sem (s2::s1::G) (tml_of_scm s1 1 ++ tml_of_scm s2 0) Stml ->
    forall x (y : Rel.T (length s2 + length s1)) h, x ~= y -> 
      Stml (Ev.env_app (s2::s1::List.nil) G (Ev.env_of_tuple _ x) h) ~= flip y.
  Proof.
    intros. destruct (j_tml_sem_app _ _ _ _ H). destruct H1. destruct H1. destruct H2.
    unfold tml_of_scm in H1.
    enough (e1 : Rel.T (length s1) = Rel.T (list_sum (List.map (length (A:=Name)) (s1 :: Datatypes.nil)))).
    enough (e2 : t Rel.V (length s2) = Rel.T (list_sum (List.map (length (A:=Name)) (s2 :: Datatypes.nil)))).
    pose (h1 := Ev.env_of_tuple (s2::List.nil) (cast _ _ e2 (fst (split y)))).
    pose (Hs1 := 
      j_tml_sem_env_app s1 (s2::List.nil) G _ H1 (snd (split y)) e1 h1 h). clearbody Hs1.
    pose (hnil := Ev.env_of_list List.nil List.nil eq_refl).
    pose (h2 := Ev.env_app (s1 :: Datatypes.nil) G (Ev.env_of_tuple (s1 :: Datatypes.nil) (cast _ _ e1 (snd (split y)))) h).
    pose (Hs2 := 
      j_tml_sem_env_app s2 List.nil (s1::G) _ H2 (fst (split y)) e2 hnil h2). clearbody Hs2.
    apply (JMeq_trans (H3 _)).
    apply (@JMeq_trans _ _ _ _
      (append (x0 (Ev.env_app _ _ h1 (Ev.env_app _ _ (Ev.env_of_tuple (s1::List.nil) (cast _ _ e1 (snd (split y)))) h)))
        (x1 (Ev.env_app _ _ hnil (Ev.env_app _ _ (Ev.env_of_tuple (s2::List.nil) (cast _ _ e2 (fst (split y)))) h2))))).
    + eapply (f_JMequal (append _) (append _)). Unshelve. eapply (f_JMeq _ _ append).
      - apply JMeq_eq. apply (f_JMeq _ _ x0). apply Ev.env_eq.
        rewrite (@projT1_env_app (s2::s1::List.nil) G).
        rewrite (@projT1_env_app (s2::List.nil) ((s1::List.nil)++G)).
        rewrite projT1_env_app. rewrite projT1_env_of_tuple. rewrite projT1_env_of_tuple.
        unfold h1. rewrite projT1_env_of_tuple.
        rewrite app_assoc. f_equal.
        transitivity (to_list (append (fst (split y)) (snd (split y)))).
        * apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
          simpl. rewrite plus_0_r. reflexivity.
          apply (split_ind y). intros. simpl. rewrite <- H4. exact H0.
          simpl. rewrite plus_0_r. reflexivity.
          simpl. rewrite plus_0_r. reflexivity.
        * rewrite to_list_append. f_equal.
          ++ apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
            simpl. rewrite plus_0_r. reflexivity.
            symmetry. apply cast_JMeq. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
          ++ apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
            simpl. rewrite plus_0_r. reflexivity.
            symmetry. apply cast_JMeq. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
      - apply (f_JMeq _ _ x1). apply Ev.env_eq.
        rewrite (@projT1_env_app (s2::s1::List.nil) G).
        rewrite (@projT1_env_app List.nil ((s2::List.nil)++((s1::List.nil)++G))).
        rewrite projT1_env_app. rewrite projT1_env_of_tuple. rewrite projT1_env_of_tuple.
        unfold h2. rewrite projT1_env_app. rewrite projT1_env_of_tuple. 
        rewrite app_assoc. rewrite app_assoc. f_equal. simpl.
        transitivity (to_list (append (fst (split y)) (snd (split y)))).
        * apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
          simpl. rewrite plus_0_r. reflexivity.
          apply (split_ind y). intros. simpl. rewrite <- H4. exact H0.
          simpl. rewrite plus_0_r. reflexivity.
          simpl. rewrite plus_0_r. reflexivity.
        * rewrite to_list_append. f_equal.
          ++ apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
            simpl. rewrite plus_0_r. reflexivity.
            symmetry. apply cast_JMeq. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
          ++ apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
            simpl. rewrite plus_0_r. reflexivity.
            symmetry. apply cast_JMeq. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
            simpl. rewrite plus_0_r. reflexivity.
      - reflexivity.
      - reflexivity.
    + apply (@JMeq_trans _ _ _ _ (append (snd (split y)) (fst (split y)))).
      - eapply (f_JMequal (append _) (append _)). Unshelve. eapply (f_JMequal append append). Unshelve.
        * unfold tml_of_scm. do 2 rewrite map_length. reflexivity.
        * exact Hs1.
        * exact Hs2.
        * unfold tml_of_scm. rewrite map_length. reflexivity.
        * unfold tml_of_scm. repeat rewrite map_length. reflexivity.
        * unfold tml_of_scm. rewrite map_length. reflexivity.
        * unfold tml_of_scm. repeat rewrite map_length. reflexivity.
      - unfold flip. apply (split_ind y). intros. reflexivity.
    + simpl. rewrite plus_0_r. reflexivity.
    + simpl. rewrite plus_0_r. reflexivity.
  Qed.

  Lemma j_tml_sem_env_app' G G2 :
    forall G1 Stml,
    Ev.j_tml_sem (G1 ++ G ++ G2) (tmlist_of_ctx_i G (length G1)) Stml ->
    forall x h1 h2, Stml (Ev.env_app _ _ h1 (Ev.env_app _ _ (Ev.env_of_tuple _ x) h2)) ~= x.
  Proof.
    induction G; simpl; intuition.
    + eapply (case0 (fun v => v ~= x) _ _). Unshelve. simpl.
      eapply (case0 (fun v => nil Rel.V ~= v) _ x). Unshelve. reflexivity.
    + destruct (j_tml_sem_app _ _ _ _ H). destruct H0. destruct H0. destruct H1.
      eapply (JMeq_trans (H2 _)).
      assert (append (fst (split x)) (snd (split x)) ~= x).
      - apply (split_ind x (fun m n p => append (fst p) (snd p) ~= x)).
        intros. rewrite H3. reflexivity.
      - eapply (JMeq_trans _ H3). Unshelve.
        eapply (f_JMequal (append _) (append _)).
        eapply (f_JMequal append append).
        * simpl. rewrite map_length. rewrite length_tmlist_of_ctx_i.
          rewrite length_concat_list_sum. reflexivity.
        * eapply (JMeq_trans _ (j_tml_sem_env_app _ _ _ _ H0 (fst (split x)) _ h1 
                  (Ev.env_app _ _ (Ev.env_of_tuple _ (cast _ _ _ (snd (split x)))) h2))). Unshelve.
          Focus 6. simpl. rewrite plus_0_r. reflexivity.
          Focus 6. reflexivity.
          ++ rewrite length_tmlist_of_ctx_i, length_concat_list_sum. reflexivity.
          ++ rewrite length_tmlist_of_ctx_i, length_concat_list_sum, map_length. reflexivity.
          ++ rewrite map_length. reflexivity.
          ++ rewrite length_tmlist_of_ctx_i, length_concat_list_sum, map_length. reflexivity. 
          ++ apply (f_JMeq _ _ x0). f_equal.
             apply Ev.env_eq. rewrite projT1_env_app. 
             rewrite (@projT1_env_app (a::List.nil) (G++G2)). 
             rewrite projT1_env_app.
             rewrite projT1_env_of_tuple. rewrite projT1_env_of_tuple.
             rewrite (@projT1_env_app (a::List.nil) G).
             rewrite projT1_env_of_tuple. simpl.
             rewrite app_assoc. f_equal. f_equal.
             apply JMeq_eq. eapply (f_JMequal to_list to_list).
            -- rewrite plus_0_r. reflexivity.
            -- symmetry. apply cast_JMeq. reflexivity.
        * (* introduce x1', H1' with better type *)
          apply (cast_elim (Ev.env ((G1 ++ (a::List.nil)) ++ G ++ G2) ->
             Rel.T (length (tmlist_of_ctx_i G (length (G1++(a::List.nil)))))) x1).
            rewrite <- app_assoc. rewrite app_length. simpl. rewrite plus_comm. reflexivity.
            intros x1' Hx1'.
          apply (cast_elim (Ev.j_tml_sem ((G1++(a::List.nil))++G++G2) (tmlist_of_ctx_i G (length (G1++a::List.nil))) x1') H1).
            generalize dependent x1'. 
            rewrite <- app_assoc. rewrite app_length. simpl. rewrite plus_comm. intros. rewrite Hx1'. reflexivity.
          intros H1' H4. 
          (* apply IHG *)
          eapply (JMeq_trans _ (IHG _ _ H1' _ (Ev.env_app _ _ h1 (Ev.env_of_tuple _ (cast _ _ _ (fst (split x))))) h2)).
            Unshelve.
            rewrite plus_0_r. reflexivity.
            rewrite plus_0_r. reflexivity.
            Focus 2. simpl. rewrite plus_0_r. reflexivity.
          eapply (f_JMequal x1 x1'). exact Hx1'. Unshelve.
            Focus 2. rewrite <- app_assoc. reflexivity.
            Focus 2. do 2 rewrite length_tmlist_of_ctx_i. rewrite <- app_assoc. reflexivity.
          apply  Ev.env_JMeq. rewrite <- app_assoc. reflexivity.
          rewrite projT1_env_app. rewrite projT1_env_app. rewrite projT1_env_app. rewrite projT1_env_app.
          rewrite (@projT1_env_app (a::G) G2). rewrite (@projT1_env_app (a::List.nil) G).
          rewrite projT1_env_of_tuple. rewrite projT1_env_of_tuple.
          simpl. rewrite <- app_assoc. rewrite <- app_assoc. f_equal. f_equal.
          apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
          ++ rewrite plus_0_r. reflexivity.
          ++ symmetry. apply cast_JMeq. reflexivity.
          ++ rewrite plus_0_r. reflexivity.
          ++ rewrite plus_0_r. reflexivity.
    Qed.

  Lemma j_btb_sem_ctx d G Gout T1 s1 T2 s2 Sbtb : 
    SQLSem3.j_btb_sem d G Gout ((T1, s1) :: (T2, s2) :: Datatypes.nil) Sbtb ->
    Gout = s1::s2::List.nil.
  Proof.
    intro. inversion H. subst.
    apply (existT_eq_elim H7); clear H7; intros _ H7.
    apply (existT_eq_elim (JMeq_eq H7)); clear H7; intros _ HSbtb.
    inversion H8. subst.
    apply (existT_eq_elim H11); clear H11; intros _ H11.
    apply (existT_eq_elim (JMeq_eq H11)); clear H11; intros _ HSbtb0.
    eapply (SQLSem3.j_nil_btb_sem _ _ _ _ _ _ H12). Unshelve. intros. subst. reflexivity.
  Qed.

  Lemma j_commutative_join d G T1 T2 s1 s2 sa sb S1 S2 h :
    length sb = length s1 + length s2 ->
    SQLSem3.j_q_sem d G sa (SELECT * FROM ((T1,s1)::(T2,s2)::List.nil) WHERE TRUE) S1 ->
    SQLSem3.j_q_sem d G sb
      (SELECT (btm_of_tml (tml_of_scm s1 1 ++ tml_of_scm s2 0) sb) FROM ((T2,s2)::(T1,s1)::List.nil) WHERE TRUE)
      S2 ->
    forall ra rb, ra ~= rb -> Rel.memb (S1 h) ra = Rel.memb (S2 h) rb.
  Proof.
    intros Hlen H H0 ra rb H1. inversion H. subst. 
    apply (existT_eq_elim H9); clear H9; intros _ H9.
    apply (existT_eq_elim (JMeq_eq H9)); clear H9; intros _ HS1.
    inversion H0. subst.
    apply (existT_eq_elim H14); clear H14; intros _ H14.
    apply (existT_eq_elim (JMeq_eq H14)); clear H14; intros _ HS2.
    subst.
    assert (HG2 : G2 = s2::s1::List.nil). eapply (j_btb_sem_ctx _ _ _ _ _ _ _ _ H9).
    assert (e' : Rel.T (length (concat G1)) = Rel.T (length (tmlist_of_ctx G1))). 
      rewrite Ev.length_tmlist, length_concat_list_sum. reflexivity.
    transitivity (Rel.memb (Rel.sum (Rel.sel (Sbtb h)
        (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
            S3.is_btrue (Sc (Ev.env_app G1 G (Ev.env_of_tuple G1 Vl) h))))
      (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
         Stml (Ev.env_app G1 G (Ev.env_of_tuple G1 Vl) h))) (cast _ _ e' ra)).
      apply eq_memb_dep. rewrite Ev.length_tmlist. reflexivity.
      apply cast_JMeq. reflexivity.
      symmetry. apply cast_JMeq. reflexivity.
      assert (eS2 : (fun _ : Ev.env G =>
        Rel.R (length (List.map snd (btm_of_tml (tml_of_scm s1 1 ++ tml_of_scm s2 0) (List.map snd tml))))) 
        ~= (fun _ : Ev.env G => Rel.R (length (List.map snd tml)))). rewrite H13. reflexivity.
      pose (HS2' := @f_JMequal _ _ _ _ eq_refl eS2 _ _ h h HS2 JMeq_refl). clearbody HS2'. simpl in HS2'.
    assert (e'' : Rel.T (length (List.map snd tml)) 
      = Rel.T (length (List.map fst (btm_of_tml (tml_of_scm s1 1 ++ tml_of_scm s2 0) (List.map snd tml))))). 
      rewrite H3, List.map_length in Hlen. do 2 rewrite List.map_length. rewrite Hlen, H3, Hlen. reflexivity.
    transitivity (Rel.memb (Rel.sum
            (Rel.sel (Sbtb0 h)
               (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G2)) =>
                S3.is_btrue (Sc0 (Ev.env_app G2 G (Ev.env_of_tuple G2 Vl) h))))
            (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G2)) =>
             Stml1 (Ev.env_app G2 G (Ev.env_of_tuple G2 Vl) h))) (cast _ _ e'' rb)).
      Focus 2. apply eq_memb_dep. rewrite <- H3. do 2 rewrite List.map_length. reflexivity.
      eapply (JMeq_trans _ HS2'). Unshelve.
      apply cast_JMeq. reflexivity.
      symmetry. apply cast_JMeq. reflexivity.
    (* get rid of trivial true conditions *)
    rewrite sel_true. Focus 2. intros. inversion H10. rewrite <- (existT_projT2_eq _ _ _ H5). reflexivity.
    rewrite sel_true. Focus 2. intros. inversion H15. rewrite <- (existT_projT2_eq _ _ _ H5). reflexivity.
    (* clear context *)
    clear Sc Sc0 H10 H15 H HS2 HS2' eS2 H0 e1 H7.
    (* simplify lhs *)
    apply (eq_memb_dep_elim1 (fun x => x = _) _ _ (Rel.sum (Sbtb h) (fun Vl => Vl))).
      rewrite Ev.length_tmlist, length_concat_list_sum. reflexivity.
      apply sum_ext_dep; auto. 
      rewrite Ev.length_tmlist, length_concat_list_sum. reflexivity.
      intros. apply (JMeq_trans H). symmetry.
    generalize dependent Stml. rewrite tmlist_of_ctx_O.
    intros.
    eapply (JMeq_trans _ (j_tml_sem_env_app' _ _ List.nil _ H11 _ (Ev.env_of_list List.nil List.nil eq_refl) h)).
    Unshelve. Focus 2.
      eapply (f_JMeq _ _ Stml). apply Ev.env_eq. rewrite projT1_env_app.
      rewrite (@projT1_env_app List.nil (G1++G)). rewrite projT1_env_app. reflexivity.
    intros. assert (Hr1 : r1 ~= ra). apply (JMeq_trans H). apply cast_JMeq. reflexivity. clear H.
    (* simplify rhs *)
    apply (cast_elim (Rel.T (length s1 + length s2)) rb).
      f_equal. exact Hlen.
      intros r2 Hr2.
    apply (cast_elim (Rel.R (length s2 + length s1)) (Sbtb0 h)).
      rewrite HG2. simpl. f_equal. omega.
      intros R2 HR2.
    transitivity (Rel.memb (Rel.sum R2 flip) r2).
      Focus 2. apply eq_memb_dep.
      rewrite <- H3, <- Hlen. do 2 rewrite List.map_length. reflexivity.
      apply sum_ext_dep.
      rewrite HG2. simpl. omega.
      rewrite <- H3, <- Hlen. do 2 rewrite List.map_length. reflexivity.
      symmetry. exact HR2.
      intros. symmetry. 
      apply (cast_elim (Ev.env (s2::s1::G) -> Rel.T (length (tml_of_scm s1 1 ++ tml_of_scm s2 0))) Stml1).
        rewrite List.app_length. unfold tml_of_scm. repeat rewrite List.map_length. 
        unfold tml_of_scm in H3. rewrite <- H3. rewrite <- Hlen. rewrite List.map_length.
        rewrite HG2. reflexivity.
      intros Stml1' HStml1'.
      apply (cast_elim (Ev.j_tml_sem (s2::s1::G) (tml_of_scm s1 1 ++ tml_of_scm s2 0) Stml1') H16).
        unfold btm_of_tml. apply JMeq_eq. 
        eapply (@f_JMequal _ (fun _ => Type) _ (fun _ => Type) _ _ 
                 (Ev.j_tml_sem (G2++G) (List.map fst (combine (tml_of_scm s1 1 ++ tml_of_scm s2 0) (List.map snd tml))))
                 (Ev.j_tml_sem (s2::s1::G) (tml_of_scm s1 1 ++ tml_of_scm s2 0)) _ _ _ HStml1'). Unshelve.
        Focus 3. rewrite HG2. simpl. rewrite H3. rewrite List.map_length.
        rewrite H13. erewrite length_combine. reflexivity.
        unfold tml_of_scm. rewrite List.app_length. do 2 rewrite List.map_length. symmetry. exact Hlen.
      intros H16' _. 
      eapply (JMeq_trans _ (j_tml_sem_flip _ _ _ _ H16' _ _ _ _)). Unshelve.
      + symmetry. apply cast_JMeq. exact Hr2.
      + do 2 rewrite Rel.p_sum.
        apply (filter_supp_elim _ (Sbtb h) r1); intro;
        apply (filter_supp_elim' _ _ R2 r2 (fun l => _ = list_sum (List.map _ l))); intro; simpl.
        - f_equal. apply (cast_elim (Rel.T (list_sum (List.map (@length _) G2))) (flip r2)).
          rewrite HG2. simpl. unfold Rel.T. f_equal. omega.
          intros fr2 Hfr2. 
          eapply (eq_trans (j_commutative_join_btb _ _ _ _ _ _ _ _ _ _ _ _ 
            fr2 (fst (split r2)) (snd (split r2)) _ _ H8 H9)). Unshelve.
          apply eq_memb_dep.
          rewrite HG2. simpl. omega.
          exact HR2. symmetry. exact Hfr2.
          apply (split_ind r2 (fun m n p => r1 ~= append (fst p) (snd p))). intros. simpl.
          rewrite <- H2. apply (JMeq_trans Hr1). apply (JMeq_trans H1). exact Hr2.
          rewrite <- Hfr2. unfold flip.
          apply (split_ind r2 (fun m n p => (let (v1,v2) := p in append v2 v1) ~= append (snd p) (fst p))). 
          intros. simpl. reflexivity.
        - enough (Rel.memb (Sbtb h) r1 > 0).
          replace (Rel.memb (Sbtb h) r1) with (Rel.memb R2 (flip r2)) in H2.
          exfalso. apply H0. apply Rel.p_fs. exact H2.
          enough (exists (rc : Rel.T (length s1)) (rd : Rel.T (length s2)), r2 ~= append rc rd /\ flip r2 ~= append rd rc).
          decompose record H4. rewrite H7.
          enough (Rel.T (length s2 + length s1) = Rel.T (list_sum (List.map (length (A:=Name)) G2))).
          transitivity (Rel.memb (Sbtb0 h) (cast _ _ H6 (append x0 x))).
          apply eq_memb_dep. rewrite HG2. simpl. omega.
          symmetry. exact HR2. symmetry. apply cast_JMeq. reflexivity.
          eapply (j_commutative_join_btb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H9 H8). Unshelve.
          rewrite HG2. f_equal. simpl. omega.
          unfold flip. 
          apply (split_ind r2 (fun m n p => exists rc rd, r2 ~= append rc rd /\ (let (v1,v2) := p in append v2 v1) ~= append rd rc)).
          intros. exists v1. exists v2. split; apply eq_JMeq; intuition.
          apply (Rel.p_fs_r _ _ _ H). Focus 3. apply cast_JMeq. reflexivity.
          apply (JMeq_trans Hr1). apply (JMeq_trans H1). apply (JMeq_trans Hr2). exact H5.
        - enough (Rel.memb R2 (flip r2) > 0).
          replace (Rel.memb R2 (flip r2)) with (Rel.memb (Sbtb h) r1) in H2.
          exfalso. apply H. apply Rel.p_fs. exact H2. 
          symmetry.
          enough (exists (rc : Rel.T (length s1)) (rd : Rel.T (length s2)), r2 ~= append rc rd /\ flip r2 ~= append rd rc).
          decompose record H4. rewrite H7.
          enough (Rel.T (length s2 + length s1) = Rel.T (list_sum (List.map (length (A:=Name)) G2))).
          transitivity (Rel.memb (Sbtb0 h) (cast _ _ H6 (append x0 x))).
          apply eq_memb_dep. rewrite HG2. simpl. omega.
          symmetry. exact HR2. symmetry. apply cast_JMeq. reflexivity.
          eapply (j_commutative_join_btb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H9 H8). Unshelve.
          f_equal. rewrite HG2. simpl. omega.
          unfold flip. 
          apply (split_ind r2 (fun m n p => exists rc rd, r2 ~= append rc rd /\ (let (v1,v2) := p in append v2 v1) ~= append rd rc)).
          intros. exists v1. exists v2. split; apply eq_JMeq; intuition.
          apply (Rel.p_fs_r _ _ _ H0). Focus 3. apply cast_JMeq. reflexivity.
          apply (JMeq_trans Hr1). apply (JMeq_trans H1). apply (JMeq_trans Hr2). exact H5.
        - reflexivity.
      + rewrite HG2. simpl. rewrite List.map_length. erewrite length_combine. reflexivity.
        rewrite List.app_length. unfold tml_of_scm. do 2 rewrite List.map_length. symmetry. exact Hlen.
      + rewrite HG2. simpl. erewrite map_fst_combine. reflexivity. 
        rewrite List.app_length. unfold tml_of_scm. do 2 rewrite List.map_length. symmetry. exact Hlen.
      + enough (forall (eG2: Rel.T (list_sum (List.map (length (A:=Name)) G2)) = 
                             Rel.T (list_sum (List.map (length (A:=Name)) (s2::s1::List.nil)))), 
          Stml1 (Ev.env_app G2 G (Ev.env_of_tuple G2 y) h) ~=
          Stml1' (Ev.env_app (s2 :: s1 :: Datatypes.nil) G 
            (Ev.env_of_tuple (s2 :: s1 :: Datatypes.nil) (cast _ _ eG2 y)) h)).
        apply H0. generalize dependent y. generalize dependent Stml1. rewrite HG2.
        intros. eapply (f_JMequal Stml1 Stml1'). Unshelve. exact HStml1'.
        apply eq_JMeq. f_equal. f_equal. symmetry. apply JMeq_eq. apply cast_JMeq. reflexivity.
        rewrite HG2. reflexivity. reflexivity.
        simpl. unfold btm_of_tml. rewrite map_fst_combine. reflexivity.
        rewrite app_length. unfold tml_of_scm. do 2 rewrite List.map_length. symmetry. exact Hlen.
      + apply cast_JMeq. symmetry. exact H.
  Qed.

  Fixpoint var_subst (a : FullVar) (n : nat) (btm : list (pretm * Name)) :=
    if (fst a =? n) then
      match btm with
      | List.nil => tmvar a
      | p::btm0 => if (Db.Name_dec (snd a) (snd p)) then (fst p) 
                   else var_subst a n btm0
      end
    else tmvar a.

  Lemma var_subst_neq n a m btm : n <> m -> var_subst (n,a) m btm = tmvar (n,a).
  Proof.
    intro. enough (n =? m = false). destruct btm; simpl; rewrite H0; reflexivity.
    destruct (n =? m) eqn:e; intuition. contradiction H.
    apply Nat.eqb_eq. exact e.
  Qed.

  Definition tm_subst (t : pretm) (n : nat) (btm : list (pretm * Name)) := 
    match t with
    | tmvar a => var_subst a n btm
    | _ => t
    end.

  Definition btm_subst (btm1 : list (pretm * Name)) (n : nat) (btm2 : list (pretm * Name)) :=
    List.map (fun p => (tm_subst (fst p) n btm2, snd p)) btm1.

  Definition btm_subst_scm (btm : list (pretm * Name)) (n : nat) (tml : list pretm) (s : Scm) :=
    btm_subst btm n (List.combine tml s).

  Definition tml_subst (tml : list pretm) (n : nat) (btm : list (pretm * Name)) :=
    List.map (fun t => tm_subst t n btm) tml.

  Definition tml_subst_scm (tml1 : list pretm) (n : nat) (tml2 : list pretm) (s : Scm) := 
    tml_subst tml1 n (List.combine tml2 s).

  Lemma j_var_append a s : j_var a s -> exists s1 s2, s = s1 ++ a :: s2 /\ ~ List.In a s1 /\ ~ List.In a s2.
  Proof.
    intro. induction H.
    + exists List.nil. exists s. intuition.
    + decompose record IHj_var. exists (b::x). exists x0. rewrite H1. simpl. intuition.
  Qed.

  Lemma var_subst_append a t l1 l2 s1 s2 : length l1 = length s1 -> ~ List.In a s1 ->
    var_subst (0, a) 0 (combine (l1 ++ t :: l2) (s1 ++ a :: s2)) = t.
  Proof.
    intro. 
    eapply (list_ind2 _ _ (fun l0 s0 => 
      ~ List.In a s0 -> var_subst (0,a) 0 (combine (l0 ++ t :: l2) (s0 ++ a :: s2)) = t) _ _ l1 s1 H).
    Unshelve.
    + simpl. destruct (Db.Name_dec a a); intuition.
    + simpl. intros. destruct (Db.Name_dec a b).
      - contradiction H2. intuition.
      - apply H1. intro. contradiction H2. intuition.
  Qed.

  Lemma j_tml_sem_append G t l1 l2 Sl : Ev.j_tml_sem G (l1 ++ t :: l2) Sl ->
    forall h (v1 : Rel.T (length l1)) (v2 : Rel.T (S (length l2))) St, 
      Sl h ~= append v1 v2 -> Ev.j_tm_sem G t St -> St h ~= hd v2.
  Proof.
    induction l1; intros.
    + simpl in H. inversion H. apply (existT_eq_elim H5); simpl; intros.
      rewrite <- H8 in H0. enough (cons _ (St0 h) _ (Stml h) ~= v2).
      rewrite <- H9. simpl. replace St0 with St. reflexivity. apply (Ev.j_tm_sem_fun _ _ _ H1 _ H4).
      apply (JMeq_trans H0). eapply (case0 (fun v0 => append v0 v2 ~= v2) _ v1). Unshelve. reflexivity.
    + simpl in H. inversion H. apply (existT_eq_elim H5); simpl; intros. clear H5 H7.
      rewrite <- H8 in H0. eapply (IHl1 _ H6 h (tl v1) v2 _ _ H1). Unshelve.
      rewrite (Vector.eta v1) in H0. simpl in H0. eapply (tl_equal _ _ _ H0). Unshelve.
      rewrite app_length. reflexivity.
  Qed.

  Lemma unnest_tm G s1 s2 t1 tml2 St1 Stml2 St0 Vl h (Hlen : length s1 = length tml2) :
    Ev.j_tm_sem (s1::G) t1 St1 ->
    Ev.j_tml_sem (s2::G) tml2 Stml2 ->
    Ev.j_tm_sem (s2::G) (tm_subst t1 0 (List.combine tml2 s1)) St0 ->
    forall Stml2', Stml2 ~= Stml2' ->
    St1 (Ev.env_app (s1::List.nil) _
      (Ev.env_of_tuple _ (Stml2' (Ev.env_app (s2::List.nil) G (Ev.env_of_tuple _ Vl) h)))
      h)
    ~= St0 (Ev.env_app (s2::List.nil) G (Ev.env_of_tuple _ Vl) h).
  Proof.
    intros. inversion H; subst.
    + simpl in H1. inversion H1; subst. reflexivity.
    + simpl in H1. inversion H1; subst. reflexivity.
    + simpl in H1. inversion H3.
      - eapply (existT_eq_elim H9). intros. subst. clear H9 H10.
        rewrite subenv1_app.
        enough (exists s s', 
                 s1 = s ++ a :: s' /\ ~ List.In a s /\ ~ List.In a s').
        decompose record H4.
        enough (exists (Wl1 : Rel.T (length x)) (Wl2 : Rel.T (S (length x0))), 
          Stml2' (Ev.env_app _ _ (Ev.env_of_tuple (s2::List.nil) Vl) h) ~= Vector.append Wl1 Wl2).
        decompose record H7. clear H4 H7.
        enough (Rel.T (length x + S (length x0)) = Rel.T (list_sum (List.map (@length _) ((x ++ a :: x0)::List.nil)))).
        apply (cast_elim (Ev.env ((x++a::x0)::List.nil) -> Value) Sa). rewrite H5. reflexivity.
        intros Sa' HSa.
        eapply (@JMeq_trans _ _ _ _ (Sa' (Ev.env_of_tuple ((x++a::x0)::List.nil) (cast _ _ H4 (Vector.append x1 x2))))).
        eapply (f_JMequal Sa Sa'). exact HSa.
        generalize dependent Stml2'. rewrite H5. intros Stml2' HStml2 Hx1x2.
        eapply (f_JMequal (Ev.env_of_tuple _) (Ev.env_of_tuple _)). Unshelve.
        reflexivity.
        symmetry. apply cast_JMeq. symmetry. exact Hx1x2.
        apply (cast_elim (Ev.j_var_sem (x++a::x0) a Sa') H8).
        generalize dependent Sa. rewrite H5. intros. rewrite HSa. reflexivity.
        intros H8' eH8.
        apply (JMeq_trans (j_var_sem_tech _ _ _ _ _ _ _ H8')).
        symmetry. enough (length tml2 = S (length x + length x0)).
        decompose record (list_length_decompose _ _ _ _ H7).
        apply (cast_elim (Ev.env ((s2::List.nil)++G) -> Rel.T (length (x4 ++ x3 :: x5))) Stml2).
        rewrite H14. reflexivity.
        intros Stml2'' HStml2''.
        apply (cast_elim (Rel.T (length x4)) x1). rewrite H12. reflexivity. intros x1' Hx1'.
        apply (cast_elim (Rel.T (S (length x5))) x2). rewrite H10. reflexivity. intros x2' Hx2'.
        apply (@JMeq_trans _ _ _ _ (hd x2')). Focus 2. generalize dependent x2'. rewrite H10. intros. rewrite Hx2'. reflexivity.
        eapply (j_tml_sem_append _ _ _ _ Stml2'' _ _ x1' x2'). Unshelve.
        enough (Stml2'' (Ev.env_app _ _ (Ev.env_of_tuple _ Vl) h) ~= Stml2' (Ev.env_app _ _ (Ev.env_of_tuple _ Vl) h)).
        apply (JMeq_trans H13). apply (JMeq_trans H11). 
        generalize dependent x2'. generalize dependent x1'. rewrite H12, H10. intros. subst. reflexivity.
        eapply (f_JMequal Stml2'' Stml2'). Unshelve. symmetry in HStml2''. apply (JMeq_trans HStml2''). exact H2.
        reflexivity.
        rewrite H14, H5 in H1. rewrite var_subst_append in H1. exact H1. exact H12. exact H6.
        rewrite <- Hlen. rewrite H5. rewrite app_length. simpl. omega.
        simpl. rewrite app_length. f_equal. simpl. omega.
        apply exists_vector_append. rewrite H5. simpl. rewrite app_length. simpl. omega.
        apply j_var_append. apply (Ev.j_var_sem_j_var _ _ _ H8).
        rewrite H5. reflexivity.
        rewrite H5. reflexivity.
        reflexivity.
        reflexivity.
        generalize dependent Stml2''. rewrite <- H14. intros. rewrite <- HStml2''. exact H0.
        reflexivity.
        rewrite <- H14. simpl. rewrite Nat.add_0_r. rewrite Hlen. reflexivity.
      - apply (existT_eq_elim H9). intros. subst. clear H9 H10.
        rewrite subenv2_app. rewrite var_subst_neq in H1.
        inversion H1. inversion H7. apply (existT_eq_elim H14). intros. subst. clear H14 H15.
        rewrite subenv2_app. rewrite (Ev.j_fvar_sem_fun _ _ _ _ H8 _ H13). reflexivity.
        omega.
  Qed.

  Lemma unnest_tml G s1 s2 tml1 tml2 Stml1 Stml2 Stml0 Vl h (Hlen : length s1 = length tml2) :
    Ev.j_tml_sem (s1::G) tml1 Stml1 ->
    Ev.j_tml_sem (s2::G) tml2 Stml2 ->
    Ev.j_tml_sem (s2::G) (tml_subst_scm tml1 0 tml2 s1) Stml0 ->
    forall Stml2', Stml2 ~= Stml2' ->
    Stml1 (Ev.env_app (s1::List.nil) _
      (Ev.env_of_tuple _ (Stml2' (Ev.env_app (s2::List.nil) G (Ev.env_of_tuple _ Vl) h)))
      h)
    ~= Stml0 (Ev.env_app (s2::List.nil) G (Ev.env_of_tuple _ Vl) h).
  Proof.
    intros. induction H.
    + simpl in H1. inversion H1. apply (existT_eq_elim H3); clear H3; intros. subst. reflexivity.
    + simpl in H1. inversion H1. apply (existT_eq_elim H7); clear H7; intros.
      rewrite <- H9. eapply (f_JMequal (cons _ _ _) (cons _ _ _)). Unshelve.
      eapply (f_JMequal (cons _ _) (cons _ _)). Unshelve.
      eapply (f_JMequal (cons _) (cons _)). reflexivity.
      eapply (unnest_tm _ _ _ _ _ _ _ _ _ _ _ H H0 H6 _ H2).
      change (length tml ~= length (List.map (fun a => tm_subst a 0 (combine tml2 s1)) tml)).
      rewrite map_length. reflexivity.
      apply IHj_tml_sem0. exact H8.
      change (Vector.t Rel.V (length tml) = Vector.t Rel.V (length (List.map (fun t2 => tm_subst t2 0 (combine tml2 s1)) tml))).
      rewrite map_length. reflexivity.
      change ((fun (_:Vector.t Rel.V (length tml)) => Vector.t Rel.V (S (length tml))) ~= (fun (_:Vector.t Rel.V (length (List.map (fun t2 => tm_subst t2 0 (combine tml2 s1)) tml))) => Vector.t Rel.V (S (length (List.map (fun t2 => tm_subst t2 0 (combine tml2 s1)) tml))))).
      repeat rewrite map_length. reflexivity.
      reflexivity. reflexivity.
      Unshelve.
      reflexivity. reflexivity. exact Hlen.
  Qed.

  Lemma eq_btm_subst_tml_subst (btm1 btm2 : list (pretm * Name)) s1 n : 
    List.map fst (btm_subst_scm btm1 n (List.map fst btm2) s1)
    = tml_subst_scm (List.map fst btm1) n (List.map fst btm2) s1.
  Proof.
    unfold btm_subst_scm, btm_subst, tml_subst_scm, tml_subst.
    induction btm1; simpl; intuition.
    f_equal. apply IHbtm1.
  Qed.

  Lemma select_unnest d G sa sb btm1 btm2 btb s1 s2 c2 Sa Sb h:
    SQLSem3.j_q_sem d G sa 
     (SELECT btm1 
      FROM ((tbquery (SELECT btm2 FROM ((btb,s2)::List.nil) WHERE c2), s1)::List.nil) 
      WHERE TRUE) Sa ->
    SQLSem3.j_q_sem d G sb 
     (SELECT (btm_subst_scm btm1 0 (List.map fst btm2) s1) 
      FROM ((btb,s2)::List.nil) 
      WHERE c2) Sb ->
    Sa h ~= Sb h.
  Proof.
    intros. inversion H. subst. 
    apply (existT_eq_elim H9); clear H9; intros _ H9.
    apply (existT_eq_elim (JMeq_eq H9)); clear H9; intros _ HSa.
    inversion H0. subst.
    apply (existT_eq_elim H13); clear H13; intros _ H13.
    apply (existT_eq_elim (JMeq_eq H13)); clear H13; intros _ HSb.
    subst. apply cast_JMeq. symmetry. apply cast_JMeq.
    inversion H7. apply (existT_eq_elim H16); clear H16; intros _ H16. 
    apply (existT_eq_elim (JMeq_eq H16)); clear H16; intros; subst. rewrite <- H19.
    eapply (SQLSem3.j_nil_btb_sem _ _ _ _ _ _ H17). Unshelve. intros. subst. rewrite <- H4.
    inversion H6. apply (existT_eq_elim H22); clear H22; intros _ H22.
    apply (existT_eq_elim (JMeq_eq H22)); clear H22; intros. subst.
    inversion H10. apply (existT_eq_elim H2); clear H2; intros _ H2. rewrite <- H2.
    inversion H21. apply (existT_eq_elim H19); clear H19; intros _ H19.
    apply (existT_eq_elim (JMeq_eq H19)); clear H19; intros. subst.
    eapply (SQLSem3.j_nil_btb_sem _ _ _ _ _ _ H23). Unshelve. intros. subst. rewrite <- H4.
    inversion H26. apply (existT_eq_elim H30); clear H30; intros _ H30.
    apply (existT_eq_elim (JMeq_eq H30)); clear H30; intros. subst. rewrite <- H33.
    inversion H27. apply (existT_eq_elim H34); clear H34; intros _ H34. 
    apply (existT_eq_elim (JMeq_eq H34)); clear H34; intros; subst. rewrite <- H37.
    eapply (SQLSem3.j_nil_btb_sem _ _ _ _ _ _ H35). Unshelve. intros. subst. rewrite <- H4.
    apply (cast_elim (Rel.R (list_sum (List.map (length (A:=Name)) (s2 :: Datatypes.nil)))) (ST h)).
      rewrite H18. simpl. f_equal. omega.
    intros RT HRT. apply (@JMeq_trans _ _ _ _ 
      (Rel.sum (Rel.sel RT (fun Vl => 
        S3.is_btrue (Sc0 (Ev.env_app _ _ (Ev.env_of_tuple (s2::List.nil) Vl) h))))
       (fun Vl => Stml0 (Ev.env_app _ _ (Ev.env_of_tuple (s2::List.nil) Vl) h)))).
    + eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMequal (@Rel.sum _ _) (@Rel.sum _ _)). Unshelve.
      reflexivity.
      eapply (f_JMequal (Rel.sel _) (Rel.sel _)). Unshelve.
      eapply (f_JMequal (@Rel.sel _) (@Rel.sel _)). Unshelve.
      reflexivity. apply cast_JMeq. apply (JMeq_trans (Rel_times_Rone _ _)). exact HRT.
      reflexivity. reflexivity. reflexivity. reflexivity.
      reflexivity. reflexivity. reflexivity. reflexivity.
      reflexivity. reflexivity.
    + apply (cast_elim (Ev.env (s2 :: G) -> Rel.T (list_sum (List.map (length (A:=Name)) (s1 :: Datatypes.nil)))) Stml1).
        rewrite map_length in H24. rewrite map_length. rewrite H24. simpl. rewrite plus_0_r. reflexivity.
      intros Stml1' HStml1.
      apply (@JMeq_trans _ _ _ _
        (Rel.sum (Rel.sum (Rel.sel RT (fun Vl =>
                     S3.is_btrue (Sc (Ev.env_app (s2 :: List.nil) G (Ev.env_of_tuple (s2 :: List.nil) Vl) h))))
                 (fun Vl => Stml1' (Ev.env_app (s2 :: List.nil) G (Ev.env_of_tuple (s2 :: List.nil) Vl) h)))
          (fun Vl => Stml (Ev.env_app (s1 :: List.nil) G (Ev.env_of_tuple (s1 :: List.nil) Vl) h)))).
      Focus 2. eapply (f_JMequal (Rel.sum _) (Rel.sum _)); try auto. Unshelve.
      eapply (f_JMequal (@Rel.sum _ _) (@Rel.sum _ _)); try auto. Unshelve.
      apply (@JMeq_trans _ _ _ _
        (cast (Rel.R (length (List.map snd btm2) + list_sum (List.map (length (A:=Name)) Datatypes.nil)))
          (Rel.R (length s1 + list_sum (List.map (length (A:=Name)) Datatypes.nil))) e2
          (Rel.times
            (cast (Rel.R (length (List.map fst btm2))) (Rel.R (length (List.map snd btm2))) e3
              (Rel.sum
                (Rel.sel
                 (cast (Rel.R (length s0 + list_sum (List.map (length (A:=Name)) Datatypes.nil)))
                    (Rel.R (length s2 + list_sum (List.map (length (A:=Name)) Datatypes.nil))) e4
                    (Rel.times (ST1 h) Rel.Rone))
                 (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) (s2 :: Datatypes.nil))) =>
                  S3.is_btrue (Sc (Ev.env_app (s2 :: Datatypes.nil) G (Ev.env_of_tuple (s2 :: Datatypes.nil) Vl) h))))
              (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) (s2 :: Datatypes.nil))) =>
               Stml1 (Ev.env_app (s2 :: Datatypes.nil) G (Ev.env_of_tuple (s2 :: Datatypes.nil) Vl) h)))) Rel.Rone))).
      symmetry. apply cast_JMeq. apply (JMeq_trans (Rel_times_Rone _ _)). apply cast_JMeq.
      apply eq_sum_dep. reflexivity. simpl. rewrite <- H24, Nat.add_0_r. repeat rewrite map_length. reflexivity.
      apply eq_sel_dep. reflexivity.
      apply cast_JMeq. apply (JMeq_trans (Rel_times_Rone _ _)).
      eapply (JMeq_trans _ HRT). Unshelve. Focus 8.
      destruct (SQLSem3.jT_sem_fun_dep _ _ _ _ _ H28 _ _ _ _ eq_refl eq_refl H13).
      generalize ST1, H28, H2. clear H H6 ST1 H21 H26 H27 H28 H2. rewrite H1.
      intros. rewrite H2. reflexivity.
      reflexivity.
      apply funext_JMeq. reflexivity. f_equal.
      simpl. rewrite <- H24. repeat rewrite map_length. omega.
      intros Wl Wl' eWl. rewrite eWl.
      eapply (f_JMequal _ _ _ _ HStml1). Unshelve. reflexivity.
      apply cast_JMeq. apply (JMeq_trans (Rel_times_Rone _ _)). apply cast_JMeq.
      eapply (JMeq_trans _ (eq_JMeq (eq_sym (sel_true _ _ _)))). Unshelve.
      reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
      simpl. rewrite <- H24. repeat rewrite map_length. rewrite Nat.add_0_r. reflexivity.
      symmetry. apply cast_JMeq. apply (JMeq_trans (Rel_times_Rone _ _)).
      apply cast_JMeq. reflexivity. intros. simpl. reflexivity.
      rewrite Rel_sum_sum. apply eq_sum_dep.
      reflexivity. unfold btm_subst_scm, btm_subst. repeat rewrite map_length. reflexivity.
      erewrite (SQLSem3.jc_sem_fun_dep _ _ _ _ H14 _ _ _ _ _ H31). Unshelve. reflexivity.
      apply funext_JMeq; try auto.
      unfold btm_subst_scm, btm_subst. repeat rewrite map_length. reflexivity.
      intros x y exy. rewrite exy. symmetry.
      generalize Stml0, H15. clear Stml0 H0 H15.
      rewrite eq_btm_subst_tml_subst. intros.
      eapply unnest_tml.
      rewrite <- H24. repeat rewrite map_length. reflexivity.
      exact H11.
      exact H32.
      exact H15.
      exact HStml1.
      reflexivity.
      reflexivity.
  Qed.


End RewriteRules.