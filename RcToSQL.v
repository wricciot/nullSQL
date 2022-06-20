Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat RcSyntax AbstractRelation Bool.Sumbool Tribool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Util Common Syntax SemFacts RelFacts Eval 
  Semantics RcSemantics.

Module RcToSql (Sem : SEM) (Rc : RC) (Sql : SQL).
  Import Db.
  Import Rc.
  Import Sql.

  Module RF := RelFacts.Facts Sql.
  Module SF := SemFacts.Facts.
  Import RF.
  Import SF.

(*
  Module S2 := Sem2 Db.
  Module S3 := Sem3 Db.
  Module SQLSem2 := SQLSemantics Db S2 Sql.
  Module SQLSem3 := SQLSemantics Db S3 Sql.
*)

  Module RCSem := RcSemantics Sem Rc.
  Module SQLSem := SQLSemantics Sem Sql.

  Fixpoint undo_bigunion q :=
    match q with
    | nil b s => Some ((b, s), List.nil)
    | union q1 q2 => bind (undo_bigunion q2) (fun r => Some ((fst (fst r), snd (fst r)), q1::snd r))
    | _ => None
    end.

  Definition sql_nil s : prequery :=
    select false (List.map (fun a => (tmnull, a)) s) List.nil cndfalse.

  Fixpoint sql_bigunion b s ql :=
    match ql with
    | List.nil => sql_nil s
    | q::List.nil => q
    | q::ql0 => qunion b q (sql_bigunion b s ql0)
    end.

  Definition sql_select b tup ql c :=
    select b tup ql c.

  Definition sql_distinct T s := selstar true (((T,s)::List.nil)::List.nil) cndtrue.

(*
  Fixpoint undo_multicomprn q :=
    match q with
    | comprn q1 q2 => 
        bind (undo_multicomprn q1) (fun r => Some (fst r, (fst (snd r), snd (snd r) ++ (q2::List.nil))))
    | single b tup => Some (b, (tup, List.nil))
    | _ => None
    end.

  Definition xlate_ncoll_fix r :=
    (* FIXME the 0s below are wrong: we need to know the arity of the query *)
    bind r (fun r' =>
    let b := fst (fst r') in let s := snd (fst r') in let ql := snd r' in
    Some (sql_bigunion b s ql)).

  Definition xlate_ndisjunct_fix r :=
    bind r (fun r' =>
     let b := fst r' in let tup := fst (snd r') in let ql := snd (snd r') in
     Some (sql_select b tup ql)).

*)

  Definition sql_empty q s := cndnot (cndex (selstar false (((tbquery q,s)::List.nil)::List.nil) cndtrue)).

(*
  Axiom rcschema : Rc.tm -> option Scm.
  Axiom rcdistinct : Rc.tm -> option bool.
*)

  (* normal form translation *)
  Inductive j_base_x (d : Db.D) : list Scm -> Rc.tm -> Sql.pretm -> Prop :=
  | jbx_cst  : forall g c, j_base_x d g (cst c) (tmconst c)
  | jbx_null : forall g, j_base_x d g null tmnull
  | jbx_proj : forall g n x,
      (* the assumption on well-formedness wrt the context can be provided separately *)
      (* List.nth_error g n = Some s -> j_var x s -> *)
      j_base_x d g (proj (var n) x) (tmvar (n,x)).

  Inductive j_basel_x (d : Db.D) : list Scm -> list Rc.tm -> list Sql.pretm -> Prop :=
  | j_blx_nil : forall g, j_basel_x d g List.nil List.nil
  | j_blx_cons : forall g t tml,
      forall t' tml',
      j_base_x d g t t' ->
      j_basel_x d g tml tml' ->
      j_basel_x d g (t::tml) (t'::tml').

  Inductive j_tuple_x (d : Db.D) : list Scm -> Rc.tm -> Scm -> list Sql.pretm -> Prop :=
  | jtx_mktup : forall g bl, 
      forall tl',
      List.NoDup (List.map fst bl) ->
      j_basel_x d g (List.map snd bl) tl' ->
      j_tuple_x d g (mktup bl) (List.map fst bl) tl'.

  Inductive j_cond_x (d : Db.D) : list Scm -> Rc.tm -> Sql.precond -> Prop :=
  | jbx_empty : forall g q b,
      forall q' s,
      j_coll_x d g q b s q' 
      -> j_cond_x d g (empty b q) (sql_empty q' s)
  | jwx_pred : forall g n p tl,
      forall tl',
      j_basel_x d g tl tl' -> length tl = n ->
      j_cond_x d g (pred n p tl) (cndpred n p tl')
  | jwx_true : forall g, j_cond_x d g rctrue cndtrue
  | jws_false : forall g, j_cond_x d g rcfalse cndfalse
  | jws_isnull : forall g t,
      forall t', j_base_x d g t t' ->
      j_cond_x d g (isnull t) (cndnull true t')
  | jws_istrue : forall g c,
      forall c', j_cond_x d g c c' ->
      j_cond_x d g (istrue c) (cndistrue c')
  | jws_and : forall g c1 c2,
      forall c1' c2', j_cond_x d g c1 c1' -> j_cond_x d g c2 c2' ->
      j_cond_x d g (rcand c1 c2) (cndand c1' c2')
  | jws_or : forall g c1 c2,
      forall c1' c2', j_cond_x d g c1 c1' -> j_cond_x d g c2 c2' ->
      j_cond_x d g (rcor c1 c2) (cndor c1' c2')
  | jws_not : forall g c,
      forall c', j_cond_x d g c c' ->
      j_cond_x d g (rcnot c) (cndnot c')


  with j_coll_x (d : Db.D) : list Scm -> Rc.tm -> bool -> Scm -> Sql.prequery -> Prop :=
  | jcx_nil : forall g b s, 
      List.NoDup s -> j_coll_x d g (nil b s) b s (sql_nil s)
  | jcx_disjunct : forall g t,
      forall b s tl' c' Bl',
      (* not union is implicity in j_disjunct_x *)
      j_disjunct_x d g t b s tl' c' Bl'  ->
      j_coll_x d g t b s (sql_select b (List.combine tl' s) Bl' c')
  | jcx_union : forall g t1 t2,
      forall b s tl1' c' Bl1' q2' ,
      j_disjunct_x d g t1 b s tl1' c' Bl1' ->
      j_coll_x d g t2 b s q2' ->
      j_coll_x d g (union t1 t2) b s (qunion (negb b) (sql_select b (List.combine tl1' s) Bl1' c') q2')

  with j_disjunct_x (d : Db.D) : list Scm -> Rc.tm -> bool -> Scm -> list Sql.pretm -> Sql.precond -> list (list (Sql.pretb * Scm)) -> Prop :=
  | jdx_single : forall g b tup c,
      forall s tl' c',
      j_tuple_x d g tup s tl' -> j_cond_x d g c c' ->
      j_disjunct_x d g (cwhere (single b tup) c) b s tl' c' List.nil
  | jdx_comprn : forall g q1 q2,
      forall b s s2 tl1' c' Bl1' T2',
      j_gen_x d g q2 b s2 T2' ->
      j_disjunct_x d (s2::g) q1 b s tl1' c' Bl1' ->
      j_disjunct_x d g (comprn q1 q2) b s tl1' c' (((T2', s2)::List.nil) :: Bl1')

  with j_gen_x (d : Db.D) : list Scm -> Rc.tm -> bool -> Scm -> Sql.pretb -> Prop :=
  | jgx_tab : forall g x,
      forall s, Db.db_schema d x = Some s ->
      j_gen_x d g (tab x) false s (tbbase x)
  | jgx_diff : forall g q1 q2,
      forall s q1' q2',
      j_coll_x d g q1 false s q1' ->
      j_coll_x d g q2 false s q2' ->
      j_gen_x d g (diff q1 q2) false s (tbquery (qexcept true q1' q2'))
  | jgx_dtab : forall g x,
      forall s, Db.db_schema d x = Some s ->
      j_gen_x d g (dist (tab x)) true s (tbquery (sql_distinct (tbbase x) s))
  | jgx_ddiff : forall g q1 q2,
      forall s q1' q2',
      j_coll_x d g q1 false s q1' ->
      j_coll_x d g q2 false s q2' ->
      j_gen_x d g (dist (diff q1 q2)) true s (tbquery (sql_distinct (tbquery (qexcept true q1' q2')) s))
  | jgx_prom : forall g q,
      forall s q',
      j_coll_x d g q true s q' -> 
      j_gen_x d g (prom q) false s (tbquery q')
  .

  Derive Inversion jbx_proj_inv with (forall d g n x t', j_base_x d g (proj (var n) x) t') Sort Prop.
  Derive Inversion jbx_empty_inv with (forall d g b q t', j_base_x d g (empty b q) t') Sort Prop.
  Derive Inversion jblx_nil_inv with (forall d g tml', j_basel_x d g List.nil tml') Sort Prop.
  Derive Inversion jblx_cons_inv with (forall d g t tml tml', j_basel_x d g (t::tml) tml') Sort Prop.
  Derive Inversion jtx_mktup_inv with (forall d g bl s tml', j_tuple_x d g (mktup bl) s tml') Sort Prop.
  Derive Inversion jwx_pred_inv with (forall d g n p tl c, j_cond_x d g (pred n p tl) c) Sort Prop.
  Derive Inversion jcx_nil_inv with (forall d g b s b' s' q', j_coll_x d g (nil b s) b' s' q') Sort Prop.
  (* Derive Inversion jcx_disjunct_inv we should know that j_disjunct_x holds and invert that one *)
  Derive Inversion jcx_union_inv with (forall d g t1 t2 b s q', j_coll_x d g (union t1 t2) b s q') Sort Prop.
  Derive Inversion jdx_single_inv with (forall d g b tup c b' s' tl' c' Bl', j_disjunct_x d g (cwhere (single b tup) c) b' s' tl' c' Bl') Sort Prop.
  Derive Inversion jdx_comprn_inv with (forall d g t1 t2 b s tl' c' Bl', j_disjunct_x d g (comprn t1 t2) b s tl' c' Bl') Sort Prop.
  Derive Inversion jgx_tab_inv with (forall d g x b s T', j_gen_x d g (tab x) b s T') Sort Prop.
  Derive Inversion jgx_diff_inv with (forall d g t1 t2 b s T', j_gen_x d g (diff t1 t2) b s T') Sort Prop.
  Derive Inversion jgx_dtab_inv with (forall d g x b s T', j_gen_x d g (dist (tab x)) b s T') Sort Prop.
  Derive Inversion jgx_ddiff_inv with (forall d g t1 t2 b s T', j_gen_x d g (dist (diff t1 t2)) b s T') Sort Prop.
  Derive Inversion jgx_prom_inv with (forall d g t b s T', j_gen_x d g (prom t) b s T') Sort Prop.

  Scheme jwx_ind_mut   := Induction for j_cond_x      Sort Prop
  with   jcx_ind_mut   := Induction for j_coll_x      Sort Prop
  with   jdx_ind_mut   := Induction for j_disjunct_x  Sort Prop
  with   jgx_ind_mut   := Induction for j_gen_x       Sort Prop.

  Combined Scheme j_x_ind_mut from jwx_ind_mut, jcx_ind_mut, jdx_ind_mut, jgx_ind_mut.

  Lemma j_basel_x_length : forall d G tl tl', j_basel_x d G tl tl' -> length tl = length tl'.
  Proof.
    intros d G tl tl' H. induction H; simpl; intuition.
  Qed.

  Lemma j_tuple_x_length : forall d G t s tl', j_tuple_x d G t s tl' -> length s = length tl'.
  Proof.
    intros d G t s tl' H. inversion H; simpl; subst.
    generalize (j_basel_x_length _ _ _ _ H1). do 2 rewrite map_length. intuition.
  Qed.

  Lemma j_disjunct_x_length : forall d G t b s tl c Bl,
    j_disjunct_x d G t b s tl c Bl ->
    List.length s = List.length tl.
  Proof.
    intros d G t b s qt c Bl H.
    eapply (jdx_ind_mut _
          (fun G0 t0 t0' _ => True)
          (fun G0 t0 b0 s0 q0 _ => True)
          (fun G0 t0 b0 s0 tml0 _ Bl0 _ => length s0 = length tml0)
          (fun G0 t0 b0 s0 T' _ => True)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    Unshelve.
    all: simpl; intuition.
    eapply j_tuple_x_length. exact j.
  Qed.

  Lemma j_coll_x_nodup_schema : forall d G t b s qt,
    j_coll_x d G t b s qt ->
    NoDup s.
  Proof.
    intros d G t b s qt Hx.
    eapply (jcx_ind_mut _
          (fun G0 t0 t0' _ => True)
          (fun G0 t0 b0 s0 q0 _ => NoDup s0)
          (fun G0 t0 b0 s0 tml0 _ Bl0 _ => NoDup s0)
          (fun G0 t0 b0 s0 T' _ => True)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx).
    Unshelve.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl. intros. inversion j. exact H0.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
  Qed.

  Lemma j_tuple_x_sem_eq : forall d G t s tml',
    j_tuple_x d G t s tml' ->
    forall s' St, RCSem.j_tuple_sem d G t s' St -> s = s'.
  Proof.
    intros d G t s tml' H. inversion H; subst.
    intros s' St H'. inversion H'; subst.
    apply map_fst_combine. exact H6.
  Qed.

  Lemma j_coll_x_sem_eq : forall d G t b s qt,
    j_coll_x d G t b s qt ->
    forall b' s' St, RCSem.j_coll_sem d G t b' s' St ->
    b = b' /\ s = s'.
  Proof.
    intros d G t b s qt Hx.
    eapply (jcx_ind_mut _
          (fun G0 t0 t0' _ => True)
          (fun G0 t0 b0 s0 q0 _ => forall b' s' St, RCSem.j_coll_sem d G0 t0 b' s' St -> b0 = b' /\ s0 = s')
          (fun G0 t0 b0 s0 tml0 _ Bl0 _ => forall b' s' St, RCSem.j_disjunct_sem d G0 t0 b' s' St -> b0 = b' /\ s0 = s')
          (fun G0 t0 b0 s0 T' _ => forall b' s' St, RCSem.j_gen_sem d G0 t0 b' s' St -> b0 = b' /\ s0 = s')
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx).
    Unshelve.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intros g0 b0 s0 Hnd b' s' St Hsem. inversion Hsem; subst. intuition. inversion H4.
    + simpl. intros g0 t0 b0 s0 tml' c' Bl' Ht0 IHt0 b' s' St Hsem. inversion Hsem; subst; inversion Ht0; subst.
      eapply IHt0. exact H4.
      eapply IHt0. exact H4.
    + simpl. intros g0 t1 t2 b0 s0 tml' c' Bl1' q2' Ht1 IHt1 Ht2 IHt2 b' s' St Hsem. inversion Hsem; subst.
      inversion H4.
      eapply IHt2. exact H7.
    + simpl. intros g0 b0 t0 c0 s0 tml' c' Ht0 Hc' _ b' s' St Hsem. inversion Hsem; subst; intuition.
      eapply j_tuple_x_sem_eq. exact Ht0. exact H5.
    + simpl. intros G0 q1 q2 b0 s0 s1 tl1' c' Bl1' T2' Hq2 IHq2 Hq1 IHq1 b' s' St Hsem. inversion Hsem; subst.
      destruct (IHq2 _ _ _ H5); subst. intuition.
      destruct (IHq1 _ _ _ H6); subst. reflexivity.
    + simpl. intros G0 x s0 Hs0 b' s' St Hsem. inversion Hsem; subst. clear H4.
      rewrite Hs0 in e; injection e; intuition.
    + simpl. intros G0 q1 q2 s0 q1' q2' Hq1 IHq1 Hq2 IHq2 b' s' St Hsem. inversion Hsem; subst.
      destruct (IHq1 _ _ _ H5); intuition.
    + simpl. intros G0 x s0 Hs0 b' s' St Hsem. inversion Hsem; subst. clear H4.
      rewrite Hs0 in e; injection e; intuition.
    + simpl. intros G0 q1 q2 s0 q1' q2' Hq1 IHq1 Hq2 IHq2 b' s' St Hsem. inversion Hsem; subst.
      destruct (IHq1 _ _ _ H5); intuition.
    + simpl. intros G0 q s0 q' Hq IHq b' s' St Hsem. inversion Hsem; subst.
      destruct (IHq _ _ _ H4). intuition.
  Qed.

  Lemma j_coll_x_sem_eq_bool : forall d G t b s qt b' s' St,
    j_coll_x d G t b s qt -> RCSem.j_coll_sem d G t b' s' St ->
    b = b'.
  Proof.
    intros. destruct (j_coll_x_sem_eq _ _ _ _ _ _ H _ _ _ H0). intuition.
  Qed.

  Lemma j_coll_x_sem_eq_scm : forall d G t b s qt b' s' St,
    j_coll_x d G t b s qt -> RCSem.j_coll_sem d G t b' s' St ->
    s = s'.
  Proof.
    intros. destruct (j_coll_x_sem_eq _ _ _ _ _ _ H _ _ _ H0). intuition.
  Qed.

  Lemma base_rcsem_to_sqlsem : forall d G t St,
    RCSem.j_base_sem d G t St ->
    forall t', j_base_x d G t t' ->
    exists St', SQLSem.j_tm_sem G t' St' /\ forall h, St' h ~= St h.
  Proof.
  intros d G t St H. elim H; simpl.
  + intros G0 c t' j; clear H. inversion j; subst.
    eexists; split. constructor. simpl; reflexivity.
  + intros G0 t' j; clear H. inversion j; subst.
    eexists; split. constructor. simpl; reflexivity.
  + intros G0 i a Sia j. clear H; intros t0' H.
    inversion H; subst. elim j; intros.
    - eexists; split. constructor. constructor. exact H0.
      reflexivity.
    - decompose record H1; rename x into Sp.
      eexists; split. constructor. constructor. exact H0. intuition.
  Qed.

  Lemma basel_rcsem_to_sqlsem : forall d G tl Stl,
    RCSem.j_basel_sem d G tl Stl ->
    forall tl', j_basel_x d G tl tl' ->
    exists Stl', SQLSem.j_tml_sem G tl' Stl' /\ forall h, Stl' h ~= Stl h.
  Proof.
    intros d G tl Stl H. elim H; simpl.
    + intros G0. clear H; intros tml0' H.
      inversion H; subst. eexists; split. constructor. simpl; intro. reflexivity.
    + intros G0 t0 tml0 St0 Stml0 jt0 jtml0 IHtml0. clear H; intros tml0' H.
      inversion H; subst. decompose record (base_rcsem_to_sqlsem _ _ _ _ jt0 _ H3); rename x into St'.
      decompose record (IHtml0 _ H5); rename x into Stml'.
      eexists; split. constructor. exact H1. exact H4.
      simpl; intro. rewrite H2. 
      clear jtml0 IHtml0. generalize dependent Stml0. replace (length tml0) with (length tml').
      intros. rewrite H6. reflexivity.
      symmetry; apply (j_basel_x_length _ _ _ _ H5).
  Qed.

  Lemma tuple_rcsem_to_sqlsem : forall d G t s St,
    RCSem.j_tuple_sem d G t s St ->
    forall tml', j_tuple_x d G t s tml' ->
      exists Stml', SQLSem.j_tml_sem G tml' Stml' /\ forall h, Stml' h ~= St h.
  Proof.
    intros d G t s St H. inversion H; subst.
    intros tml' Html'. inversion Html'; subst.
    enough (List.map snd (combine s bl) = bl). rewrite H3 in H7.
    decompose record (basel_rcsem_to_sqlsem _ _ _ _ H6 _ H7); rename x into Stml'.
    eexists; split. exact H9.
    apply (existT_eq_elim H0); intros. apply (existT_eq_elim (JMeq_eq H11)); intros.
    rewrite <- H13. symmetry. apply cast_fun_app_JM; try intuition.
    rewrite (j_tuple_x_length _ _ _ _ _ Html'); reflexivity.
    rewrite <- H14. symmetry; apply H10.
    apply map_snd_combine. exact H2.
  Qed.

  Lemma tml_sem_tmlist_of_ctx_eq s G :
    forall s0 Stml,
      SQLSem.j_tml_sem ((s0++s)::G) (tmlist_of_ctx (s::List.nil)) Stml ->
        Stml ~= fun h => Evl.tuple_of_env (s::List.nil) (Evl.env_skip (@Evl.subenv1 ((s0 ++ s)::List.nil) G h)).
  Proof.
    elim s.
    + simpl. unfold tmlist_of_ctx. simpl. intros.
      eapply (SQLSem.j_tml_nil_sem _ _ (fun _ _ => _) _ H). Unshelve.
      simpl. intros _ Heq. eapply (existT_eq_elim Heq); clear Heq; intros _ Heq.
      symmetry. eapply (JMeq_trans _ Heq). Unshelve.
      apply funext_JMeq. reflexivity. reflexivity.
      intros h1 h2 Hh; subst.
      eapply (Vector.case0 (fun x => x ~= _)). reflexivity.
    + simpl. unfold tmlist_of_ctx. simpl. intros.
      eapply (SQLSem.j_tml_cons_sem _ _ _ _ (fun _ _ _ _ => _ ~= _) _ H0). Unshelve.
      simpl; intros; subst. eapply (existT_eq_elim H6); clear H6; intros _ H6.
      symmetry. eapply (JMeq_trans _ H6). Unshelve.
      apply funext_JMeq. reflexivity. simpl. f_equal; f_equal. rewrite app_length. rewrite map_length. reflexivity.
      intros h1 h2 Hh; subst.
      inversion H2. subst.
      enough (Evl.j_fvar_sem ((s0 ++ a :: l) :: G) 0 a St) as H7'.
      generalize (Evl.j_fvar_sem_inside_eq _ _ _ _ _ H7'). intro Ht.
      (* Ht is what we need for the hd *)
      enough (exists Stml', SQLSem.j_tml_sem (((s0 ++ a :: List.nil) ++ l)::G) (List.map (fun x => tmvar (0,x)) l ++ List.nil) Stml' /\ Stml' ~= Stml0).
      decompose record H3. rename x into Stml'; clear H3.
      generalize (H _ _ H6). intro Html.
      rewrite (Vector.eta (Evl.tuple_of_env _ (Evl.env_skip (@Evl.subenv1 ((s0++a::l)::List.nil) _ h2)))).
      apply cons_equal.
      - rewrite Ht. apply Evl.hd_tuple_of_env.
      - rewrite app_length. rewrite map_length. reflexivity.
      - rewrite (Evl.tl_tuple_of_env a l List.nil _).
        enough (exists (h : Evl.env (((s0 ++ a :: List.nil) ++ l) :: G)), h ~= h2).
        decompose record H3; clear H3; rename x into h.
        apply (@JMeq_trans _ _ _ _ (Stml' h)).
        apply (@JMeq_trans _ _ _ _ 
          (Evl.tuple_of_env (l::List.nil) (Evl.env_skip (@Evl.subenv1 (((s0 ++ a :: List.nil)++l)::List.nil) _ h)))).
        apply (f_JMeq _ _ (Evl.tuple_of_env (l::List.nil))). apply JMeq_eq.
        rewrite <- Evl.env_skip_single. symmetry. apply Evl.env_skip_skip.
        eapply (f_JMequal (@Evl.subenv1 (((s0++a::List.nil)++l)::List.nil) G) (@Evl.subenv1 ((s0++a::l)::List.nil) G)).
        simpl. rewrite <- app_assoc. reflexivity. exact H5.
        erewrite (f_JMequal _ _ h h Html JMeq_refl). reflexivity.
        eapply (f_JMequal Stml' Stml0 h h2 H8 H5).
        rewrite <- app_assoc. exists h2. reflexivity.
        Unshelve.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc, app_length, map_length. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
      - rewrite <- app_assoc. eexists. split. exact H4. reflexivity.
      - exact H7.
  Qed.

  Lemma tml_sem_tmlist_of_ctx s G :
    forall s0, NoDup (s0++s) -> exists Stml,
      SQLSem.j_tml_sem ((s0++s)::G) (tmlist_of_ctx (s::List.nil)) Stml.
  Proof.
    induction s; intros.
    + simpl. eexists. constructor.
    + simpl.
      enough (exists Stml', SQLSem.j_tml_sem ((s0 ++ a :: s)::G) (tmlist_of_ctx (s::List.nil)) Stml').
      decompose record H0; rename x into Stml.
      decompose record (Evl.j_fvar_sem_inside _ _ _ G H); rename x into Sa.
      eexists. constructor. constructor. exact H2.
      exact H1. replace (s0 ++ a :: s) with ((s0 ++ a :: List.nil) ++ s).
      apply IHs. rewrite <- app_assoc. exact H. rewrite <- app_assoc. reflexivity.
  Qed.

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

  Lemma env_skip_nil : forall s' G' h', @Evl.env_skip s' G' List.nil h' = h'.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma qunion_sem d G s b q1 q2 :
    forall Sq1 Sq2,
    SQLSem.j_q_sem d G s q1 Sq1 ->
    SQLSem.j_q_sem d G s q2 Sq2 ->
    exists Sq, SQLSem.j_q_sem d G s (qunion b q1 q2) Sq
      /\ forall h, Sq h = if b then(Rel.plus (Sq1 h) (Sq2 h)) else (Rel.flat (Rel.plus (Sq1 h) (Sq2 h))).
  Proof.
    intros. eexists; split. constructor. exact H. exact H0.
    simpl. intro. reflexivity.
  Qed.

(*
  Lemma sql_select_sem d G s b tl Bl c :
    length tl = length s ->
    forall G1 SBl Sc Stl,
     SQLSem.j_btbl_sem d G G1 Bl SBl ->
     SQLSem.j_cond_sem d (G1 ++ G) c Sc ->
     SQLSem.j_tml_sem (G1 ++ G) tl Stl ->
    exists Sq, SQLSem.j_q_sem d G s (sql_select b (combine tl s) Bl c) Sq
    /\ forall h, Sq h ~= let S1 := SBl h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Evl.env_app _ _ (Evl.env_of_tuple G1 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stl(Evl.env_app _ _ (Evl.env_of_tuple G1 Vl) h) in
                  let S := Rel.sum S2 f
                  in if b then Rel.flat S else S.
  Proof.
    intro. rewrite <- (map_fst_combine _ _ _ _ H) at .
    intros. eexists; split. constructor. exact H0. exact H1.
      rewrite map_fst_combine.
*)

  Lemma sql_distinct_sem d G s T ST :
    NoDup s -> SQLSem.j_tb_sem d G s T ST ->
    exists Sq, SQLSem.j_q_sem d G s (sql_distinct T s) Sq
      /\ forall h, Sq h = Rel.flat (ST h).
  Proof.
    intros. decompose record (tml_sem_tmlist_of_ctx s G List.nil H); rename x into Stml.
    eexists; split.
      constructor. constructor. constructor. exact H0. constructor. reflexivity.
      constructor. constructor. exact H1. simpl. rewrite app_nil_r. reflexivity.
      Unshelve. shelve.
      simpl. rewrite length_tmlist. simpl. rewrite app_nil_r. reflexivity.
      simpl. rewrite <- plus_n_O. reflexivity.
      reflexivity.
    Unshelve.
    intro; simpl. f_equal.
    apply JMeq_eq. apply cast_JMeq.
    eapply (JMeq_trans (sum_id _ _ _ _ _ _)).
    erewrite sel_true.
    eapply (JMeq_trans (rsum_id _ _ _ _ _ _)).
    apply Rel_times_Rone.
    intros; simpl. apply Sem.is_btrue_btrue.
    Unshelve.
    + rewrite length_tmlist; simpl; rewrite app_length; reflexivity.
    + intro Vl; simpl.
      enough (forall h0, Stml h0 ~= Evl.tuple_of_env (s::List.nil) (Evl.env_skip (@Evl.subenv1 ((List.nil ++ s)::List.nil) G h0))).
      eapply (JMeq_trans (H2 _)). 
      rewrite env_skip_nil. rewrite subenv1_app. unfold Evl.env_app; simpl. unfold Evl.tuple_of_env; simpl.
      apply cast_JMeq. rewrite app_nil_r. eapply (JMeq_trans (Evl.of_list_to_list_opp _ _ _)).
      apply (split_ind Vl). intros; subst. apply (Vector.case0 (fun v0 => fst (v1, v0) ~= append v1 v0)).
      symmetry. apply vector_append_nil_r.
      intro. eapply (f_JMequal Stml (fun h1 => Evl.tuple_of_env (s::List.nil) (Evl.env_skip (@Evl.subenv1 ((List.nil ++ s)::List.nil) G h1))) _ _ _ _).
        Unshelve.
        reflexivity. simpl. rewrite length_tmlist. simpl. rewrite app_length. reflexivity.
        eapply tml_sem_tmlist_of_ctx_eq. exact H1. reflexivity.
    + reflexivity.
    + intros. simpl. apply cast_JMeq. apply Rel_Rone_times.
  Qed.

  Lemma eq_plus_dep m n (e : m = n) :
    forall (r1 r2 : Rel.R m) (r1' r2' : Rel.R n),
    r1 ~= r1' -> r2 ~= r2' -> Rel.plus r1 r2 ~= Rel.plus r1' r2'.
  Proof.
    rewrite e. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma eq_flat_dep m n (e : m = n) :
    forall (r1 : Rel.R m) (r2 : Rel.R n),
    r1 ~= r2 -> Rel.flat r1 ~= Rel.flat r2.
  Proof.
    rewrite e. intros. rewrite H. reflexivity.
  Qed.

  Lemma sql_null_tml_sem G s :
    exists Stml,
    SQLSem.j_tml_sem G (List.map fst (List.map (fun a : Name => (NULL, a)) s)) Stml.
  Proof.
    induction s; simpl.
    + eexists. constructor.
    + decompose record IHs; rename x into Stml; clear IHs.
      eexists. constructor. constructor. exact H.
  Qed.

  Lemma sql_nil_sem d G s :
    exists Snil,
    SQLSem.j_q_sem d G s (sql_nil s) Snil /\ (forall h, Snil h ~= RCSem.sem_nil (length s)).
  Proof.
    decompose record (sql_null_tml_sem G s); rename x into Snull.
    enough (length (List.map fst (List.map (fun a : Name => (NULL, a)) s)) = length s).
    eexists; split. constructor. constructor. constructor. exact H.
    elim s; simpl; intuition. rewrite <- H1. reflexivity.
    simpl. intro. apply cast_JMeq.
    apply p_ext_dep. exact H0.
    intros. transitivity 0.
    + rewrite Rel.p_sum. 
      replace (Rel.supp (Rel.sel Rel.Rone (fun _ => Sem.is_btrue Sem.bfalse))) with (@List.nil (Rel.T 0)). 
      reflexivity. 
      symmetry. destruct (Rel.supp (Rel.sel Rel.Rone (fun _ => Sem.is_btrue Sem.bfalse))) eqn:e. reflexivity.
      assert (Rel.memb (Rel.sel Rel.Rone (fun _ : Rel.T 0 => Sem.is_btrue Sem.bfalse)) t > 0).
      apply Rel.p_fs_r. rewrite e. constructor. reflexivity.
      erewrite Rel.p_self in H2. contradiction (lt_irrefl _ H2).
      apply Sem.is_btrue_bfalse.
      Unshelve. rewrite H0. reflexivity.
    + unfold RCSem.sem_nil. rewrite Rel.p_self. reflexivity. reflexivity.
    + elim s; simpl; intuition.
  Qed.

  Lemma flat_sem_nil n : Rel.flat (RCSem.sem_nil n) = RCSem.sem_nil n.
  Proof.
    apply Rel.p_ext; intros. rewrite Rel.p_flat.
    replace (Rel.memb (RCSem.sem_nil n) t) with O. reflexivity.
    symmetry; unfold RCSem.sem_nil. rewrite sel_false. apply Rel.p_nil.
    intros; reflexivity.
  Qed.

  Lemma sum_Rnil_sem_nil n (f : Rel.T 0 -> Rel.T n) : Rel.sum Rel.Rnil f = RCSem.sem_nil n.
  Proof.
    apply Rel.p_ext; intros.
    unfold RCSem.sem_nil. rewrite sel_false; try intuition. rewrite Rel.p_nil.
    rewrite Rel.p_sum. replace (Rel.supp Rel.Rnil) with (@List.nil (Rel.T 0)). reflexivity.
    destruct (Rel.supp Rel.Rnil) eqn:e; intuition.
    generalize (Rel.p_fs_r _ Rel.Rnil t0). rewrite Rel.p_nil, e. simpl; intro.
    assert (t0 = t0 \/ List.In t0 l). intuition. generalize (H H0). intro. inversion H1.
  Qed.

  Theorem j_tml_sem_fun_dep :
    forall G tml Stml, SQLSem.j_tml_sem G tml Stml -> forall G0 tml0 Stml0, G = G0 -> tml = tml0 -> 
      SQLSem.j_tml_sem G0 tml0 Stml0 -> Stml ~= Stml0.
  Proof.
    intros; subst. apply eq_JMeq. apply (SQLSem.j_tml_sem_fun _ _ _ H _ H2).
  Qed.

  Theorem rcsem_to_sqlsem : forall d G t b s St,
    RCSem.j_coll_sem d G t b s St ->
    forall qt, j_coll_x d G t b s qt ->
    exists Sqt, SQLSem.j_q_sem d G s qt Sqt /\ forall h, Sqt h ~= St h.
  Proof.
    intros d G t b s St H.
    eapply (RCSem.jcs_ind_mut _
          (fun G0 t0 S0 _ => forall ct0, j_cond_x d G0 t0 ct0 ->
            exists Sct0, SQLSem.j_cond_sem d G0 ct0 Sct0 /\ forall h, Sct0 h ~= S0 h)
          (fun G0 t0 b0 s0 S0 _ => forall qt0, j_coll_x d G0 t0 b0 s0 qt0 ->
            exists Sqt0, SQLSem.j_q_sem d G0 s0 qt0 Sqt0 /\ forall h, Sqt0 h ~= S0 h)
          (fun G0 t0 b0 s0 S0 _ => forall tml0' c0' Bl0', j_disjunct_x d G0 t0 b0 s0 tml0' c0' Bl0' -> 
            exists G1 Stml0' Sc0' SBl0',
              SQLSem.j_tml_sem (G1 ++ G0) tml0' Stml0' /\ SQLSem.j_cond_sem d (G1 ++ G0) c0' Sc0'
              /\ SQLSem.j_btbl_sem d G0 G1 Bl0' SBl0'
              /\ forall h, 
                  (let S1 := SBl0' h in
                  let p  := fun Vl => Sem.is_btrue (Sc0' (Evl.env_app _ _ (Evl.env_of_tuple G1 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml0' (Evl.env_app _ _ (Evl.env_of_tuple G1 Vl) h) in
                  let S := Rel.sum S2 f
                  in if b0 then Rel.flat S else S)
                  ~= S0 h)
(*
            exists Sqt0, SQLSem2.j_q_sem d G0 s0 (sql_select b0 (List.combine tml0' s0) Bl0') Sqt0
              /\ forall h, Sqt0 h ~= S0 h)
*)
          (fun G0 t0 b0 s0 S0 _ => forall st0 Tt0, j_gen_x d G0 t0 b0 st0 Tt0 ->
            s0 = st0 /\
            exists STt0, SQLSem.j_tb_sem d G0 s0 Tt0 STt0
              /\ forall h, STt0 h ~= S0 h)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  Unshelve.
  (*-- mutual induction cases: base --*)
  + simpl. intros G0 q0 b0 s0 Sq0 Hq0 IHq0. clear H; intros ct0 H.
    inversion H; subst.
    destruct (j_coll_x_sem_eq _ _ _ _ _ _ H4 _ _ _ Hq0); subst.
    decompose record (IHq0 _ H4). rename x into Sq'.
    eexists; split. constructor. constructor. constructor. constructor. constructor. constructor. exact H2.
    constructor. reflexivity. constructor. constructor.
    simpl. intro. apply eq_JMeq.
    enough (forall x, Sem.of_bool (x =? 0) = Sem.bneg (Sem.of_bool (0 <? x))).
    unfold RCSem.sem_empty. rewrite H1. f_equal. f_equal. f_equal.
    rewrite sel_true. apply eq_card_dep. 
      omega. Unshelve. Focus 4. reflexivity. Focus 4. reflexivity. 
    simpl.
    apply (@trans_JMeq _ _ _ _ (Rel.rsum (Sq' h) (fun Vl => Rel.Rsingle Vl))).
      apply eq_rsum_dep. omega. omega. apply Rel_times_Rone.
      apply funext_JMeq. f_equal; omega. f_equal; omega. intros.
      apply (trans_JMeq (Rel_Rone_times _ _)).
      eapply (f_JMequal (@Rel.Rsingle (length s0 + 0)) (@Rel.Rsingle _)).
      apply (f_JMeq _ _ Rel.Rsingle). Unshelve. 
      rewrite plus_n_O. reflexivity. exact H5.
      4: { rewrite <- plus_n_O; reflexivity. }
      4: { rewrite <- plus_n_O; reflexivity. }
    rewrite rsum_single. apply H3.
    intros _ _. apply Sem.is_btrue_btrue.
    intro. rewrite Sem.bneg_of_bool. destruct x; reflexivity.
  + simpl. intros G0 n0 p0 tml0 Stml0 Hlen Html0. clear H; intros ct0 H.
    inversion H; subst.
    decompose record (basel_rcsem_to_sqlsem _ _ _ _ Html0 _ H5). rename x into Stl'.
    apply (existT_eq_elim H1). intros _ Hp. subst; clear H1.
    enough (length tl' = length tml0).
    eexists; split. constructor. exact H2. 
      Unshelve. shelve. shelve. exact H0. Unshelve.
    clear H2. generalize dependent Stl'. rewrite H0. intros.
    rewrite H3. reflexivity.
    rewrite (j_basel_x_length _ _ _ _ H5). reflexivity.
  + simpl. intros G0. clear H; intros ct0 H.
    inversion H; subst. eexists; split. constructor. simpl; intuition.
  + simpl. intros G0. clear H; intros ct0 H.
    inversion H; subst. eexists; split. constructor. simpl; intuition.
  + simpl. intros G0 t0 St0 Ht0. clear H; intros ct0 H.
    inversion H; subst.
    decompose record (base_rcsem_to_sqlsem _ _ _ _ Ht0 _ H2). rename x into St'.
    eexists; split. constructor. exact H1. simpl; intro. rewrite H3. reflexivity.
  + simpl. intros G0 c Sc. clear H; intros Hc IHc c0 H.
    inversion H; subst. decompose record (IHc _ H2).
    eexists; split. constructor. exact H1.
    intro; simpl. rewrite H3. reflexivity.
  + simpl. intros G0 c1 c2 Sc1 Sc2. clear H; intros Hc1 IHc1 Hc2 IHc2 c' H.
    inversion H; subst.
    decompose record (IHc1 _ H3). clear IHc1; rename x into Sc1'; rename H1 into IHc1.
    decompose record (IHc2 _ H5). clear IHc2; rename x into Sc2'; rename H1 into IHc2.
    eexists; split. constructor. exact IHc1. exact IHc2.
    simpl; intro. rewrite H2, H4. reflexivity.
  + simpl. intros G0 c1 c2 Sc1 Sc2. clear H; intros Hc1 IHc1 Hc2 IHc2 c' H.
    inversion H; subst.
    decompose record (IHc1 _ H3). clear IHc1; rename x into Sc1'; rename H1 into IHc1.
    decompose record (IHc2 _ H5). clear IHc2; rename x into Sc2'; rename H1 into IHc2.
    eexists; split. constructor. exact IHc1. exact IHc2.
    simpl; intro. rewrite H2, H4. reflexivity.
  + simpl. intros G0 c Sc. clear H; intros Hc IHc c0 H.
    inversion H; subst.
    decompose record (IHc _ H2). clear IHc; rename x into Sc1; rename H1 into IHc.
    eexists; split. constructor. exact IHc.
    simpl; intro. rewrite H3. reflexivity.
  (*-- mutual inuction cases: collection --*)
  + simpl; intros G0 b0 s0 Hnd. simpl. clear H; intros qt0 H.
    eapply (jcx_nil_inv _ _ _ _ _ _ _ 
             (fun dd GG bb ss bb' ss' qq' =>
               exists Sqt0, SQLSem.j_q_sem d GG ss' qq' Sqt0 /\
               forall h, Sqt0 h ~= RCSem.sem_nil (length ss'))
               _ _ H). Unshelve.
    - simpl; intros; subst; clear H4 H5. apply sql_nil_sem.
    - simpl; intros; subst. inversion H1.
  + simpl; intros G0 t0 b0 s0 St0 jt0 IHt0. clear H; intros qt0 H.
    inversion H; subst.
    - inversion jt0.
    - decompose record (IHt0 _ _ _ H0); rename x into G1; rename x0 into Stl'; rename x1 into SBl'.
      enough (exists Stl'', SQLSem.j_tml_sem (G1 ++ G0) (List.map fst (List.combine tl' s0)) Stl'').
      decompose record H4; rename x into Stml''. eexists; split. constructor.
      * exact H3.
      * exact H2.
      * exact H6.
      * symmetry; eapply map_snd_combine. symmetry; apply (j_disjunct_x_length _ _ _ _ _ _ _ _ H0).
      * intro. generalize (j_disjunct_x_length _ _ _ _ _ _ _ _ H0); intro.
        rewrite <- H5. simpl. destruct b0; simpl.
        ++ apply eq_flat_dep. apply H7.
           apply cast_JMeq. apply eq_sum_dep; intuition.
           erewrite map_fst_combine. reflexivity. symmetry; apply H7.
           generalize dependent Stml''. erewrite map_fst_combine. intuition.
           rewrite (SQLSem.j_tml_sem_fun _ _ _ H1 _ H6). reflexivity.
           rewrite H7; reflexivity.
        ++ apply cast_JMeq. apply eq_sum_dep; intuition.
           erewrite map_fst_combine. reflexivity. symmetry; apply H7.
           generalize dependent Stml''. erewrite map_fst_combine. intuition.
           rewrite (SQLSem.j_tml_sem_fun _ _ _ H1 _ H6). reflexivity.
           rewrite H7; reflexivity.
      * replace (List.map fst (combine tl' s0)) with tl'. eexists; exact H1.
        symmetry; apply map_fst_combine. symmetry; apply (j_disjunct_x_length _ _ _ _ _ _ _ _ H0).
        Unshelve.
        generalize (j_disjunct_x_length _ _ _ _ _ _ _ _ H0); intro Hlen.
        erewrite map_fst_combine. rewrite Hlen; reflexivity. rewrite Hlen; reflexivity.
    - inversion jt0.
  + simpl; intros G0 t1 t2 b0 s0 St1 St2 jt1 IHt1 jt2 IHt2. clear H; intros qt0 H.
    eapply (jcx_union_inv _ _ _ _ _ _ _
             (fun dd GG tt1 tt2 bb ss qq' =>
               exists Sqt0, SQLSem.j_q_sem d G0 ss qq' Sqt0 /\
               forall h, Sqt0 h ~= (if b0 then Rel.flat (Rel.plus (St1 h) (St2 h)) else Rel.plus (St1 h) (St2 h)))
             _ _ H). Unshelve.
    - simpl; intros; subst. inversion H1.
    - simpl; intros; subst; clear H0.
      decompose record (IHt2 _ H7); clear IHt2; rename x into Sq2'.
      decompose record (IHt1 _ _ _ H3); clear IHt1. 
      rename x into G1; rename x0 into Stl1'; rename x1 into Sc'; rename x2 into SBl1'.
      enough (exists Stl1'', SQLSem.j_tml_sem (G1 ++ G0) (List.map fst (combine tl1' s0)) Stl1'').
      decompose record H6; clear H6; rename x into Stl1''.
      assert (length tl1' = length s0). symmetry. apply (j_disjunct_x_length _ _ _ _ _ _ _ _ H3).
      epose (Hq := (SQLSem.jqs_sel _ _ b0 _ _ _ _ _ _ _ s0 _ H5 H4 H9 _)).
        Unshelve. shelve. shelve. 
        rewrite (map_fst_combine _ _ _ _ H6), H6; reflexivity.
        rewrite (map_snd_combine _ _ _ _ H6); reflexivity.
        Unshelve.
      clearbody Hq.
      decompose record (qunion_sem _ _ _ (negb b0) _ _ _ _ Hq H1); rename x into Squ.
      exists Squ; split. exact H11.
      intro. rewrite H12; clear H12. destruct b0; simpl.
      * apply eq_JMeq. f_equal. apply JMeq_eq. apply eq_plus_dep. reflexivity.
        rewrite <- H8. apply eq_flat_dep. symmetry; exact H6.
        apply cast_JMeq. generalize dependent Stl1''. rewrite (map_fst_combine _ _ _ _ H6). intros.
        rewrite (SQLSem.j_tml_sem_fun _ _ _ H0 _ H9). reflexivity.
        apply H2.
      * eapply eq_plus_dep. reflexivity.
        apply cast_JMeq. rewrite <- H8.
        generalize dependent Stl1''. rewrite (map_fst_combine _ _ _ _ H6). intros.
        rewrite (SQLSem.j_tml_sem_fun _ _ _ H0 _ H9). reflexivity.
        apply H2.
      * replace (List.map fst (combine tl1' s0)) with tl1'. eexists; exact H0.
        symmetry. apply map_fst_combine. symmetry. apply (j_disjunct_x_length _ _ _ _ _ _ _ _ H3).
  (*-- mutual induction cases: disjunct --*)
  + simpl; intros G0 b0 tup c stup Stup Sc jtup jc IHc. clear H; intros tml0' c0' Bl0' H.
    inversion H; simpl; subst. clear H3.
    decompose record (tuple_rcsem_to_sqlsem _ _ _ _ _ jtup _ H9). rename x into Stml0'.
    decompose record (IHc _ H10). rename x into Sc0'.
    exists List.nil. eexists. eexists. eexists. split. exact H1.
    split. exact H3.
    split. constructor. intro. simpl. rewrite env_app_nil_l.
    (* TODO : lemmatize *)
    generalize (j_disjunct_x_length _ _ _ _ _ _ _ _ H). intro Hlen. 
    rewrite H4. destruct (Sem.is_btrue (Sc h)).
    - rewrite sel_true. rewrite sum_Rone_Rsingle, flat_Rsingle.
      clear jtup. generalize dependent Stup. rewrite Hlen; intros. rewrite H2. destruct b0; reflexivity.
      reflexivity.
    - rewrite sel_false. rewrite sum_Rnil_sem_nil, flat_sem_nil, Hlen. destruct b0; reflexivity. intuition.
  + simpl; intros G0 q1 q2 b0 sq2 Sq2 sq1 Sq1 e jq2 IHq2 jq1 IHq1. clear H; intros tml0' c0' Bl0' H.
    inversion H; subst.
    simpl; intros; subst. decompose record (IHq2 _ _ H3); rename x into ST2'; subst.
    decompose record (IHq1 _ _ _ H9); rename x into G1; rename x0 into Stml0'; rename x1 into Sc0'; rename x2 into SBl1'.
    enough (exists Stml0'', SQLSem.j_tml_sem ((G1 ++ (s2 :: List.nil)) ++ G0) tml0' Stml0'').
    decompose record H6; rename x into Stml0''.
    enough (exists Sc0'', SQLSem.j_cond_sem d ((G1 ++ (s2 :: List.nil)) ++ G0) c0' Sc0'').
    decompose record H10; rename x into Sc0''.
    eexists; eexists; eexists; eexists. split. exact H8.
    split. exact H11.
    split. constructor. constructor. exact H1. constructor. reflexivity. exact H5.
    simpl; intros; subst. shelve.
    rewrite <- app_assoc; eexists; exact H2.
    rewrite <- app_assoc; eexists; exact H0.
    Unshelve.
    f_equal. do 3 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. omega.
    reflexivity.
    (* involved equational reasoning *)
    generalize H7; clear H7. destruct b0; intro H7.
    - generalize (j_disjunct_x_length _ _ _ _ _ _ _ _ H9); intro Hlen. 
      rewrite eq_sum_rsum.
      rewrite sel_rsum. rewrite rsum_rsum.
      apply (@JMeq_trans _ _ _ _ (Rel.flat (Rel.rsum (Sq2 h) (fun Vl : Rel.T (length s2) => Rel.sum
       (Rel.sel
          (SBl1'
             (Evl.env_app (s2 :: Datatypes.nil) G0
                (Evl.env_of_tuple (s2 :: Datatypes.nil) (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h))
          (fun Wl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
           Sem.is_btrue
             (Sc0'
                (Evl.env_app G1 (s2 :: G0) (Evl.env_of_tuple G1 Wl)
                   (Evl.env_app (s2 :: Datatypes.nil) G0
                      (Evl.env_of_tuple (s2 :: Datatypes.nil)
                         (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h)))))
       (fun Wl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
        Stml0'
          (Evl.env_app G1 (s2 :: G0) (Evl.env_of_tuple G1 Wl)
             (Evl.env_app (s2 :: Datatypes.nil) G0
                (Evl.env_of_tuple (s2 :: Datatypes.nil) (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h))) )))).
      * apply eq_flat_dep. reflexivity.
        apply eq_rsum_dep.
          omega. reflexivity. apply cast_JMeq. apply (JMeq_trans (Rel_times_Rone _ _)). apply H4.
        apply funext_JMeq. rewrite e; reflexivity. reflexivity.
        intros. rewrite eq_sum_rsum.
        enough (Rel.T (list_sum (List.map (length (A:=Name)) G1) + (length s2 + 0))
                = Rel.T (list_sum (List.map (length (A:=Name)) (G1 ++ s2::List.nil)))).
        apply (@JMeq_trans _ _ _ _
          (Rel.rsum
            (Rel.sel (Rel.times (SBl1' (Evl.env_app _ _ (Evl.env_of_tuple (s2::List.nil) x) h)) (Rel.Rsingle x))
              (fun Vl => Sem.is_btrue (Sc0'' (Evl.env_app _ _ (Evl.env_of_tuple (G1++s2::List.nil) (cast _ _ H13 Vl)) h))))
            (fun x0 => Rel.Rsingle (Stml0'' (Evl.env_app _ _ (Evl.env_of_tuple (G1 ++ s2 :: Datatypes.nil) (cast _ _ H13 x0)) h))))).
        apply eq_rsum_dep.
          do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
          reflexivity.
        apply eq_sel_dep.
          do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        apply cast_JMeq. apply eq_times_dep. reflexivity. reflexivity.
        apply eq_JMeq. f_equal. reflexivity.
        apply funext_JMeq. do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. simpl. reflexivity.
        reflexivity.
        intros. apply eq_JMeq. f_equal. f_equal. apply Evl.env_eq. simpl. f_equal. f_equal. f_equal.
        symmetry. apply JMeq_eq. apply cast_JMeq. symmetry. exact H14.
        apply funext_JMeq. do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. simpl. reflexivity.
        reflexivity.
        intros. apply eq_JMeq. f_equal. f_equal. apply Evl.env_eq. simpl. f_equal. f_equal. f_equal.
        symmetry. apply JMeq_eq. apply cast_JMeq. symmetry. exact H14.

        rewrite sel_times_single. rewrite rsum_times_single.
        apply eq_rsum_dep; try reflexivity. apply eq_sel_dep; try reflexivity.
        apply (f_JMeq _ _ SBl1'). f_equal. f_equal. apply JMeq_eq. symmetry; apply cast_JMeq; symmetry. exact H12.
        apply eq_JMeq. extensionality Vl. f_equal. apply JMeq_eq. eapply (f_JMequal Sc0'' Sc0').
        eapply (SQLSem.jc_sem_fun_dep _ _ _ _ H11 _ _ _ _ _ H2). Unshelve.
        apply Evl.env_JMeq. rewrite <- app_assoc. reflexivity. simpl. rewrite app_assoc. f_equal.
        do 2 rewrite projT1_env_of_tuple.
        transitivity (to_list (append Vl x)).
        apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
        eapply (f_JMeq _ _ (@to_list _)). do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        apply cast_JMeq. reflexivity.
        rewrite to_list_append. f_equal.
        generalize dependent y. rewrite e. simpl. intros. rewrite H12.
        rewrite app_nil_r. apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
          eapply (f_JMeq _ _ (@to_list _)). omega. symmetry. apply fst_split_0_r.
        apply eq_JMeq. extensionality Vl.
        f_equal. apply JMeq_eq. eapply (f_JMequal Stml0'' Stml0').
        eapply (j_tml_sem_fun_dep _ _ _ H8 _ _ _ _ _ H0). Unshelve.
        apply Evl.env_JMeq. rewrite <- app_assoc. reflexivity. simpl. rewrite app_assoc. f_equal.
        do 2 rewrite projT1_env_of_tuple.
        transitivity (to_list (append Vl x)).
        apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
        eapply (f_JMeq _ _ (@to_list _)). do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        apply cast_JMeq. reflexivity.
        rewrite to_list_append. f_equal.
        generalize dependent y. rewrite e. simpl. intros. rewrite H12.
        rewrite app_nil_r. apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
          eapply (f_JMeq _ _ (@to_list _)). omega. symmetry. apply fst_split_0_r.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        reflexivity.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        f_equal. omega.
        apply funext_JMeq. f_equal. omega. reflexivity. intuition.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        reflexivity.
        Unshelve.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        f_equal. omega.
        apply funext_JMeq. f_equal. omega. reflexivity. intuition.
      * apply (@trans_JMeq _ _ _ _ 
          (Rel.flat
            (Rel.rsum (Sq2 h)
               (fun Vl : Rel.T (length s2) => Rel.flat (
                Rel.sum
                  (Rel.sel
                     (SBl1'
                        (Evl.env_app (s2 :: Datatypes.nil) G0
                           (Evl.env_of_tuple (s2 :: Datatypes.nil)
                              (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h))
                     (fun Wl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
                      Sem.is_btrue
                        (Sc0'
                           (Evl.env_app G1 (s2 :: G0) (Evl.env_of_tuple G1 Wl)
                              (Evl.env_app (s2 :: Datatypes.nil) G0
                                 (Evl.env_of_tuple (s2 :: Datatypes.nil)
                                    (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h)))))
                  (fun Wl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
                   Stml0'
                     (Evl.env_app G1 (s2 :: G0) (Evl.env_of_tuple G1 Wl)
                        (Evl.env_app (s2 :: Datatypes.nil) G0
                           (Evl.env_of_tuple (s2 :: Datatypes.nil)
                              (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h)))))))).
      erewrite (flat_rsum_flat _ 
        (fun Vl => Rel.sum (Rel.sel
              (SBl1' (Evl.env_app _ _ (Evl.env_of_tuple (s2 :: Datatypes.nil) (cast _ _ e Vl)) h))
              (fun Wl  => Sem.is_btrue (Sc0' (Evl.env_app _ _ (Evl.env_of_tuple G1 Wl) 
                (Evl.env_app _ _ (Evl.env_of_tuple (s2 :: Datatypes.nil) (cast _ _ e Vl)) h)))))
          (fun Wl => Stml0' (Evl.env_app _ _ (Evl.env_of_tuple G1 Wl) (Evl.env_app _ _
             (Evl.env_of_tuple (s2 :: Datatypes.nil) (cast _ _ e Vl)) h))))). reflexivity.
      eapply (f_JMequal (@Rel.flat _) (@Rel.flat _)). Unshelve.
      rewrite Hlen. reflexivity.
      eapply (f_JMequal (Rel.rsum (Sq2 h)) (Rel.rsum (Sq2 h))).
      rewrite Hlen. reflexivity.
      apply funext_JMeq; try reflexivity. rewrite Hlen; reflexivity.
      intros. subst. apply H7.
      rewrite Hlen; reflexivity.
      rewrite Hlen; reflexivity.
      Unshelve. rewrite Hlen. reflexivity. rewrite Hlen. reflexivity.

    - generalize (j_disjunct_x_length _ _ _ _ _ _ _ _ H9); intro Hlen. 
      rewrite eq_sum_rsum. 
      rewrite sel_rsum. rewrite rsum_rsum.
      apply (@JMeq_trans _ _ _ _ (Rel.rsum (Sq2 h) (fun Vl : Rel.T (length s2) => Rel.sum
       (Rel.sel
          (SBl1'
             (Evl.env_app (s2 :: Datatypes.nil) G0
                (Evl.env_of_tuple (s2 :: Datatypes.nil) (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h))
          (fun Wl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
           Sem.is_btrue
             (Sc0'
                (Evl.env_app G1 (s2 :: G0) (Evl.env_of_tuple G1 Wl)
                   (Evl.env_app (s2 :: Datatypes.nil) G0
                      (Evl.env_of_tuple (s2 :: Datatypes.nil)
                         (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h)))))
       (fun Wl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
        Stml0'
          (Evl.env_app G1 (s2 :: G0) (Evl.env_of_tuple G1 Wl)
             (Evl.env_app (s2 :: Datatypes.nil) G0
                (Evl.env_of_tuple (s2 :: Datatypes.nil) (cast (Rel.T (length s2)) (Rel.T (length s2 + 0)) e Vl)) h)))))).
      * apply eq_rsum_dep.
          omega. reflexivity. apply cast_JMeq. apply (JMeq_trans (Rel_times_Rone _ _)). apply H4.
        apply funext_JMeq. rewrite e; reflexivity. reflexivity.
        intros. rewrite eq_sum_rsum.
        enough (Rel.T (list_sum (List.map (length (A:=Name)) G1) + (length s2 + 0))
                = Rel.T (list_sum (List.map (length (A:=Name)) (G1 ++ s2::List.nil)))).
        apply (@JMeq_trans _ _ _ _
          (Rel.rsum
            (Rel.sel (Rel.times (SBl1' (Evl.env_app _ _ (Evl.env_of_tuple (s2::List.nil) x) h)) (Rel.Rsingle x))
              (fun Vl => Sem.is_btrue (Sc0'' (Evl.env_app _ _ (Evl.env_of_tuple (G1++s2::List.nil) (cast _ _ H13 Vl)) h))))
            (fun x0 => Rel.Rsingle (Stml0'' (Evl.env_app _ _ (Evl.env_of_tuple (G1 ++ s2 :: Datatypes.nil) (cast _ _ H13 x0)) h))))).
        apply eq_rsum_dep.
          do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
          reflexivity.
        apply eq_sel_dep.
          do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        apply cast_JMeq. apply eq_times_dep; try reflexivity.
        apply funext_JMeq. do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. simpl. reflexivity.
        reflexivity.
        intros. apply eq_JMeq. f_equal. f_equal. apply Evl.env_eq. simpl. f_equal. f_equal. f_equal.
        symmetry. apply JMeq_eq. apply cast_JMeq. symmetry. exact H14.
        apply funext_JMeq. do 2 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. simpl. rewrite app_length. simpl. reflexivity.
        reflexivity.
        intros. apply eq_JMeq. f_equal. f_equal. apply Evl.env_eq. simpl. f_equal. f_equal. f_equal.
        symmetry. apply JMeq_eq. apply cast_JMeq. symmetry. exact H14.

        rewrite sel_times_single. rewrite rsum_times_single.
        apply eq_rsum_dep; try reflexivity. apply eq_sel_dep; try reflexivity.
        apply (f_JMeq _ _ SBl1'). f_equal. f_equal. apply JMeq_eq. symmetry; apply cast_JMeq; symmetry. exact H12.
        apply eq_JMeq. extensionality Vl. f_equal. apply JMeq_eq. eapply (f_JMequal Sc0'' Sc0').
        eapply (SQLSem.jc_sem_fun_dep _ _ _ _ H11 _ _ _ _ _ H2). Unshelve.
        apply Evl.env_JMeq. rewrite <- app_assoc. reflexivity. simpl. rewrite app_assoc. f_equal.
        do 2 rewrite projT1_env_of_tuple.
        transitivity (to_list (append Vl x)).
        apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
        eapply (f_JMeq _ _ (@to_list _)). do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        apply cast_JMeq. reflexivity.
        rewrite to_list_append. f_equal.
        generalize dependent y. rewrite e. simpl. intros. rewrite H12. 
        rewrite app_nil_r. apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
          eapply (f_JMeq _ _ (@to_list _)). omega. symmetry. apply fst_split_0_r.
        apply eq_JMeq. extensionality Vl.
        f_equal. apply JMeq_eq. eapply (f_JMequal Stml0'' Stml0').
        eapply (j_tml_sem_fun_dep _ _ _ H8 _ _ _ _ _ H0). Unshelve.
        apply Evl.env_JMeq. rewrite <- app_assoc. reflexivity. simpl. rewrite app_assoc. f_equal.
        do 2 rewrite projT1_env_of_tuple.
        transitivity (to_list (append Vl x)).
        apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
        eapply (f_JMeq _ _ (@to_list _)). do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        apply cast_JMeq. reflexivity.
        rewrite to_list_append. f_equal.
        generalize dependent y. rewrite e. simpl. intros. rewrite H12.
        rewrite app_nil_r. apply JMeq_eq. eapply (f_JMequal (@to_list _ _) (@to_list _ _)).
          eapply (f_JMeq _ _ (@to_list _)). omega. symmetry. apply fst_split_0_r.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        reflexivity.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        f_equal. omega. apply funext_JMeq; try reflexivity. f_equal. omega.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        reflexivity.
        Unshelve.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        do 2 rewrite <- length_concat_list_sum.
        rewrite concat_app. rewrite app_length. simpl. rewrite app_length. reflexivity.
        f_equal. omega. apply funext_JMeq; try reflexivity. f_equal. omega.
      * assert (length tml0' = length sq1). rewrite Hlen. reflexivity.
        eapply (f_JMequal (Rel.rsum (Sq2 h)) (Rel.rsum (Sq2 h))).
        rewrite H12. reflexivity.
        apply funext_JMeq; try reflexivity. rewrite H12; reflexivity.
        intros. subst. apply H7. 
        Unshelve. rewrite H12; reflexivity. rewrite H12; reflexivity.
  (*-- mutual induction cases: gen --*)
  + simpl; intros G0 x0 s0 e0. clear H; intros st0 Tt0 Hx0.
    inversion Hx0; subst. rewrite e0 in H1. injection H1; intuition.
    eexists; split. constructor. Unshelve. 
    intro; reflexivity.
  + simpl; intros G0 t0 s0 St0 jt0 IHt0. clear H; intros st0 Tt0 Ht0.
    inversion Ht0; subst. enough (s0 = st0). subst. decompose record (IHt0 _ H1); subst; rename x into Sq'.
    intuition. eexists; split. constructor; exact H0. exact H2.
    rewrite (j_coll_x_sem_eq_scm _ _ _ _ _ _ _ _ _ H1 jt0); reflexivity.
  + simpl; intros G0 t1 t2 s0 St1 St2 jt1 IHt1 jt2 IHt2. clear H. intros st0 Tt0 H.
    inversion H; subst. enough (s0 = st0). subst.
    decompose record (IHt1 _ H3). decompose record (IHt2 _ H4). rename x into Sq1'; rename x0 into Sq2'.
    intuition. eexists; split. constructor. constructor. exact H1. exact H5.
    simpl; intro. rewrite H2, H6. reflexivity.
    rewrite (j_coll_x_sem_eq_scm _ _ _ _ _ _ _ _ _ H3 jt1); reflexivity.
  + simpl; intros G0 x0 s0 e0. clear H; intros st0 Tt0 Hx0.
    inversion Hx0; subst. rewrite e0 in H1. injection H1; intuition.
    generalize e0; clear e0; rewrite H; intro.
    assert (NoDup st0). apply (db_schema_nodup _ _ _ e0).
    epose (Hq := (sql_distinct_sem d G0 st0 (tbbase x0) _ _ _)); clearbody Hq.
      Unshelve. shelve. shelve. exact H0. constructor.
      Unshelve. decompose record Hq; clear Hq; rename x into Sq.
    eexists; split. constructor. exact H3. intro; apply eq_JMeq; apply H4.
  + simpl; intros G0 t1 t2 s0 St1 St2 jt1 IHt1 jt2 IHt2. clear H. intros st0 Tt0 H.
    inversion H; subst. enough (s0 = st0). subst.
    decompose record (IHt1 _ H3). decompose record (IHt2 _ H4). rename x into Sq1'; rename x0 into Sq2'.
    intuition. 
    assert (NoDup st0). apply (j_coll_x_nodup_schema _ _ _ _ _ _ H3).
    epose (Hq := (sql_distinct_sem d G0 st0 (tbquery (q1' EXCEPT ALL q2')) _ _ _)); clearbody Hq.
      Unshelve. shelve. shelve. shelve. exact H0. constructor. constructor. exact H1. exact H5.
      Unshelve. decompose record Hq; clear Hq; rename x into Sq.
    eexists; split. constructor. exact H8. intro; rewrite <- H2, <- H6, H9; reflexivity.
    rewrite (j_coll_x_sem_eq_scm _ _ _ _ _ _ _ _ _ H3 jt1); reflexivity.
  Qed.

End RcToSql.