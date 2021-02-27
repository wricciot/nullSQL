Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat RcSyntax AbstractRelation Bool.Sumbool Tribool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Util Common Syntax SemFacts RelFacts Eval 
  Semantics RcSemantics.

Module RcToSql (Db : DB) (Sem : SEM Db) (Rc : RC Db) (Sql : SQL Db).
  Import Db.
  Import Rc.
  Import Sql.

  Module RF := RelFacts.Facts Db Sql.
  Module SF := SemFacts.Facts Db.
  Import RF.
  Import SF.

(*
  Module S2 := Sem2 Db.
  Module S3 := Sem3 Db.
  Module SQLSem2 := SQLSemantics Db S2 Sql.
  Module SQLSem3 := SQLSemantics Db S3 Sql.
*)

  Module RCSem := RcSemantics Db Sem Rc.
  Module SQLSem := SQLSemantics Db Sem Sql.

  Module Ev := Evl Db.

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

  Axiom of_precond : precond -> pretm.

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
(*      List.NoDup (List.map fst bl) -> *)
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

  with j_coll_x (d : Db.D) : list Scm -> Rc.tm -> bool -> Scm -> Sql.prequery -> Prop :=
  | jcx_nil : forall g b s, 
      j_coll_x d g (nil b s) b s (sql_nil s)
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
    generalize (j_basel_x_length _ _ _ _ H0). do 2 rewrite map_length. intuition.
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
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    Unshelve.
    all: simpl; intuition.
    eapply j_tuple_x_length. exact j.
  Qed.

  Lemma j_tuple_x_sem_eq : forall d G t s tml',
    j_tuple_x d G t s tml' ->
    forall s' St, RCSem.j_tuple_sem d G t s' St -> s = s'.
  Proof.
    intros d G t s tml' H. inversion H; subst.
    intros s' St H'. inversion H'; subst.
    apply map_fst_combine. exact H5.
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
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx).
    Unshelve.
    + simpl; intuition.
    + simpl; intuition.
    + simpl; intros g0 b0 s0 b' s' St Hsem. inversion Hsem; subst. intuition. inversion H4.
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
    - eexists; split. constructor. constructor. 
      (* XXX exact H0. doesn't work -- apparently here Coq doesn't know that RC and SQL use the same Eval *)
      admit.
      simpl; intro. (* this will actually be reflexivity after we fix the problem above *) admit.
    - decompose record H1; rename x into Sp.
      eexists; split. constructor. constructor.
      (* XXX exact H0. doesn't work -- apparently here Coq doesn't know that RC and SQL use the same Eval *)
      admit.
      simpl; intro. (* this will actually be reflexivity after we fix the problem above *) admit.
    Unshelve. (* will go away after metavariables are instantiated *) admit. admit.
  Admitted.

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
      simpl; intro.
      (* rewrite H2, H6. up to JMeq reasoning *) admit.
  Admitted.

  Lemma tuple_rcsem_to_sqlsem : forall d G t s St,
    RCSem.j_tuple_sem d G t s St ->
    forall tml', j_tuple_x d G t s tml' ->
      exists Stml', SQLSem.j_tml_sem G tml' Stml' /\ forall h, Stml' h ~= St h.
  Proof.
    intros d G t s St H. inversion H; subst.
    intros tml' Html'. inversion Html'; subst.
    enough (List.map snd (combine s bl) = bl). rewrite H3 in H5.
    decompose record (basel_rcsem_to_sqlsem _ _ _ _ H6 _ H5); rename x into Stml'.
    eexists; split. exact H8.
    (* by JMeq transitivity, dependent equational reasoning using e and H9 and H0, where the equality is expressed using sigma types... *) admit.
    apply map_snd_combine. exact H2.
  Admitted.

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
                  let p  := fun Vl => Sem.is_btrue (Sc0' (Ev.env_app _ _ (Ev.env_of_tuple G1 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml0' (Ev.env_app _ _ (Ev.env_of_tuple G1 Vl) h) in
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
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  Unshelve.
  (*-- mutual induction cases: base --*)
  + simpl. intros G0 q0 b0 s0 Sq0 Hq0 IHq0. clear H; intros ct0 H.
    inversion H; subst.
    destruct (j_coll_x_sem_eq _ _ _ _ _ _ H4 _ _ _ Hq0); subst.
    decompose record (IHq0 _ H4). rename x into Sq'.
    eexists; split. constructor. constructor. constructor. constructor. constructor. constructor. exact H2.
    constructor. reflexivity. constructor. constructor.
    simpl.
    (* TODO: calculations with dependent types *) admit. 
    (* the following will go away *)
    Unshelve. admit. admit.
  + simpl. intros G0 n0 p0 tml0 Stml0 Hlen Html0. clear H; intros ct0 H.
    inversion H; subst.
    decompose record (basel_rcsem_to_sqlsem _ _ _ _ Html0 _ H5). rename x into Stl'.
    eexists; split. constructor. exact H2.
    simpl; intro.
    (* TODO: equational reasoning with dep types *)
    admit.
    (* the following will go away *)
    Unshelve. admit.
  (*-- mutual induction cases: collection --*)
  + simpl; intros G0 b0 s0. simpl. clear H; intros qt0 H.
    eapply (jcx_nil_inv _ _ _ _ _ _ _ 
             (fun dd GG bb ss bb' ss' qq' =>
               exists Sqt0, SQLSem.j_q_sem d GG ss' qq' Sqt0 /\
               forall h, Sqt0 h ~= RCSem.sem_nil (length ss'))
               _ _ H). Unshelve.
    - simpl; intros; subst; clear H4 H5.
      (* XXX: we need to factor out the proof that the semantics of sql_nil is the same as RCSem.sem_nil *)
      admit.
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
      * intro. rewrite <- H5. simpl. (* reasoning on terms that depend on equations *) admit.
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
      eexists. split. constructor. constructor.
      exact H5. exact H4. exact H9.
      symmetry. apply map_snd_combine. symmetry. apply (j_disjunct_x_length _ _ _ _ _ _ _ _ H3).
      exact H1.
      intro.
      (* here the rewriting is blocked by the presence of an admit-related metavariable, which will go away,
         but there's also some reasoning on equastions and casts that must disappear.
         We also need to use a rewrite <- H6, and a destruct b0 because of the test on (negb b0) *)
      admit.
      replace (List.map fst (combine tl1' s0)) with tl1'. eexists; exact H0.
      symmetry. apply map_fst_combine. symmetry. apply (j_disjunct_x_length _ _ _ _ _ _ _ _ H3).
      Unshelve.
      generalize (j_disjunct_x_length _ _ _ _ _ _ _ _ H3); intro Hlen.
      erewrite map_fst_combine. rewrite Hlen; reflexivity. rewrite Hlen; reflexivity.
  (*-- mutual induction cases: disjunct --*)
  + simpl; intros G0 b0 tup c stup Stup Sc jtup jc IHc. clear H; intros tml0' c0' Bl0' H.
    inversion H; simpl; subst. clear H3.
    decompose record (tuple_rcsem_to_sqlsem _ _ _ _ _ jtup _ H9). rename x into Stml0'.
    decompose record (IHc _ H10). rename x into Sc0'.
    exists List.nil. eexists. eexists. eexists. split. exact H1.
    split. exact H3.
    split. constructor.
    (* factorize the else branch, and prove it's equivalent to a singleton;
       then prove flat is invariant on singletons

       BUT ACTUALLY we should expect this point will include a where condition (see note A)!
       so for the moment let's _not_ consider it
     *)
    admit.
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
    simpl; intros; subst. (* XXX: proving the equality here will be involved! (B) *)
    admit.
    rewrite <- app_assoc; eexists; exact H2.
    rewrite <- app_assoc; eexists; exact H0.
    Unshelve.
    f_equal. do 3 rewrite <- length_concat_list_sum. rewrite concat_app. rewrite app_length. omega.
    reflexivity.
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
    eexists; split. constructor. constructor. constructor. constructor.
    - constructor.
    - constructor.
    - shelve.
    - constructor.
    - constructor.
    - (* XXX: semantics of: s::G |- tmlist(s) = environment projection -- do we have the proof? (13) *)
      admit.
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl.
      (* a rather convoluted equational reasoning: perhaps we can factorize it
         it probably boils down to proving some eta-equality for sum *)
      admit.
    (* these will go away by themselves *)
    Unshelve.
    admit. admit. admit. admit. admit. admit. admit.
  + simpl; intros G0 t1 t2 s0 St1 St2 jt1 IHt1 jt2 IHt2. clear H. intros st0 Tt0 H.
    inversion H; subst. enough (s0 = st0). subst.
    decompose record (IHt1 _ H3). decompose record (IHt2 _ H4). rename x into Sq1'; rename x0 into Sq2'.
    intuition. 
    eexists; split. constructor. constructor. constructor. constructor. constructor. constructor.
    - exact H1.
    - exact H5.
    - constructor.
    - reflexivity.
    - constructor.
    - constructor.
    - (* XXX: semantics of: s::G |- tmlist(s) = environment projection -- do we have the proof? (13) *)
      admit.
    - simpl; rewrite app_nil_r; reflexivity.
    - simpl.
      (* a rather convoluted equational reasoning: perhaps we can factorize it *)
      admit.
    - rewrite (j_coll_x_sem_eq_scm _ _ _ _ _ _ _ _ _ H3 jt1); reflexivity.
    (* these will go away by themselves *)
    Unshelve.
    admit. admit. admit. admit.
  Admitted.

  Lemma tml_sem_tmlist_of_ctx s G :
    forall s0 Stml,
      SQLSem.j_tml_sem ((s0++s)::G) (tmlist_of_ctx (s::List.nil)) Stml ->
        Stml ~= fun h => Ev.tuple_of_env (s::List.nil) (Ev.env_skip (@Ev.subenv1 ((s0 ++ s)::List.nil) G h)).
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
      enough (Ev.j_fvar_sem ((s0 ++ a :: l) :: G) 0 a St) as H7'.
      generalize (Ev.j_fvar_sem_inside _ _ _ _ _ H7'). intro Ht.
      (* Ht is what we need for the hd *)
      enough (exists Stml', SQLSem.j_tml_sem (((s0 ++ a :: List.nil) ++ l)::G) (List.map (fun x => tmvar (0,x)) l ++ List.nil) Stml' /\ Stml' ~= Stml0).
      decompose record H3. rename x into Stml'; clear H3.
      generalize (H _ _ H6). intro Html.
      rewrite (Vector.eta (Ev.tuple_of_env _ (Ev.env_skip (@Ev.subenv1 ((s0++a::l)::List.nil) _ h2)))).
      apply cons_equal.
      - rewrite Ht. (* can't look into tuple_of_env *) admit.
      - rewrite app_length. rewrite map_length. reflexivity.
      - rewrite (Ev.tl_tuple_of_env a l List.nil _).
        enough (exists (h : Ev.env (((s0 ++ a :: List.nil) ++ l) :: G)), h ~= h2).
        decompose record H3; clear H3; rename x into h.
        apply (@JMeq_trans _ _ _ _ (Stml' h)).
        apply (@JMeq_trans _ _ _ _ 
          (Ev.tuple_of_env (l::List.nil) (Ev.env_skip (@Ev.subenv1 (((s0 ++ a :: List.nil)++l)::List.nil) _ h)))).
        apply (f_JMeq _ _ (Ev.tuple_of_env (l::List.nil))). apply JMeq_eq.
        rewrite <- Ev.env_skip_single. symmetry. apply Ev.env_skip_skip.
        eapply (f_JMequal (@Ev.subenv1 (((s0++a::List.nil)++l)::List.nil) G) (@Ev.subenv1 ((s0++a::l)::List.nil) G)).
        simpl. rewrite <- app_assoc. reflexivity. exact H5.
        erewrite (f_JMequal _ _ h h Html JMeq_refl). reflexivity.
        eapply (f_JMequal Stml' Stml0 h h2 H8 H5).
        rewrite <- app_assoc. exists h2. reflexivity.
        Unshelve.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. (* some problems because SQLSem.Ev doesn't match Ev *) admit.
        rewrite <- app_assoc. reflexivity.
        rewrite <- app_assoc. reflexivity.
      - rewrite <- app_assoc. eexists. split. exact H4. reflexivity.
      - (* it's just Hseven *) admit.
  Admitted.


End RcToSql.

(*
BIGGIES
-------

A) add where conditions to comprehensions in RC

B) the comprehension case appears to be involved!


MEDIUM
------

Implement rsum
Convoluted equational reasonings in some cases like dist.


SMALLISH
--------

5) semantics of complex SQL terms

12) factorizing the semantics of sql_distinct is a good idea!

13) do we have the proof that [| s::G |- tmlist(s) |] is an env (s::G) -> env [s] projection?



TRAINING
--------

revise working with dep types, JMeq and casts

*)