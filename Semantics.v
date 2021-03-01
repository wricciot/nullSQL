Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Util RelFacts Common Eval.

Module SQLSemantics (Sem: SEM) (Sql : SQL).
  Import Db.
  Import Sem.
  Import Sql.
(*  Module Ev := Evl Db. *)
  Import Evl.

  Inductive j_tm_sem0 (G:Ctx) : pretm -> (env G -> Value) -> Prop :=
  | jts_const : forall c, j_tm_sem0 G (tmconst c) (fun _ => Db.c_sem c)
  | jts_null  : j_tm_sem0 G tmnull (fun _ => None)
  | jts_var   : forall i a, 
      forall Sia,
      j_fvar_sem G i a Sia -> j_tm_sem0 G (tmvar (i,a)) Sia.

  Inductive j_tml_sem0 (G:Ctx) : forall (tml : list pretm), (env G -> Rel.T (List.length tml)) -> Prop :=
  | jtmls_nil  : j_tml_sem0 G List.nil (fun _ => Vector.nil _)
  | jtmls_cons : forall t tml,
      forall St Stml,
      j_tm_sem0 G t St -> j_tml_sem0 G tml Stml ->
      j_tml_sem0 G (t::tml) (fun h => Vector.cons _ (St h) _ (Stml h)).

  Derive Inversion j_tml_nil_sem with (forall G S, j_tml_sem0 G List.nil S).
  Derive Inversion j_tml_cons_sem with (forall G t tml Stml, j_tml_sem0 G (t::tml) Stml) Sort Prop.

  (* we need to fool the kernel, because it doesn't accept instantiation to inductive types *)
  Definition j_tm_sem := j_tm_sem0.
  Definition j_tml_sem := j_tml_sem0.

  Theorem j_tm_sem_fun :
    forall G t St, j_tm_sem G t St -> forall St0, j_tm_sem G t St0 -> St = St0.
  Proof.
    intros G t St Ht. induction Ht.
    + intros. inversion H. reflexivity.
    + intros. inversion H. reflexivity.
    + intros. inversion H0. apply (j_fvar_sem_fun _ _ _ _ H _ H4).
  Qed.

  Theorem j_tml_sem_fun :
    forall G tml Stml, j_tml_sem G tml Stml -> forall Stml0, j_tml_sem G tml Stml0 -> Stml = Stml0.
  Proof.
    intros G tml Stml Html. induction Html.
    + intros. inversion H. apply (existT_eq_elim H1); clear H1; intros; subst. reflexivity.
    + intros. inversion H0. apply (existT_eq_elim H4); clear H4; intros; subst.
      rewrite (j_tm_sem_fun _ _ _ H _ H3). rewrite (IHHtml _ H5). reflexivity.
  Qed.

  Lemma j_tm_sem_weak G G' t St (Ht : j_tm_sem G t St) :
    j_tm_sem (G' ++ G) (tm_lift t (length G')) (fun h => St (subenv2 h)).
  Proof.
    elim Ht; try (intros; constructor).
    elim G'. 
    + replace Sia with (fun h => Sia (@subenv2 List.nil _ h)) in H. exact H. 
      extensionality h. destruct h. f_equal. apply env_eq. reflexivity.
    + intros. simpl. pose (H0' := jfs_tl a0 _ _ _ _ H0); clearbody H0'.
      enough (forall A (f : A -> Prop) x y, x = y -> f x -> f y). generalize H0'. apply H1.
      extensionality h. destruct h. f_equal. apply env_eq. unfold subenv2. simpl.
      rewrite skipn_skipn. f_equal. repeat rewrite app_length. simpl. omega.
      intros A f x y Hxy. rewrite Hxy. intuition.
  Qed.

  Lemma j_var_sem_j_var s x Sa (H : j_var_sem s x Sa) : j_var x s.
  Proof.
    induction H; constructor; intuition.
  Qed.

  (* alternate -- not stronger but easier -- version of sum *)

  Axiom R_sum : forall m n, Rel.R m -> (Rel.T m -> Rel.R n) -> Rel.R n.
  Implicit Arguments R_sum [m n].

  (* singleton rel *)
  Definition R_single {m} : Rel.T m -> Rel.R m :=
    fun t => Rel.sum Rel.Rone (fun _ => t).


  (* NOTE: the ordering in the LATERAL list of lists grows dependencies left to right, while each of the 
     inner lists has the same ordering (right to left) as contexts *)
  Inductive j_q_sem (d : Db.D) : forall G (s : Scm), prequery -> (env G -> Rel.R (List.length s)) -> Prop := 
  | jqs_sel : forall G b tml btbl c,
      forall G0 Sbtbl Sc Stml s e,
      j_btbl_sem d G G0 btbl Sbtbl ->
      j_cond_sem d (G0++G) c Sc ->
      j_tml_sem (G0++G) (List.map fst tml) Stml -> 
      s = List.map snd tml ->
      j_q_sem d G s (select b tml btbl c) 
        (fun h => let S1 := Sbtbl h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Evl.env_app _ _ (Evl.env_of_tuple G0 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml (Evl.env_app _ _ (Evl.env_of_tuple G0 Vl) h) in
                  let S := cast _ _ e (Rel.sum S2 f)
                  in if b then Rel.flat S else S)
  | jqs_selstar : forall G b btbl c,
      forall s0 G0 Sbtbl Sc Stml e,
      j_btbl_sem d G G0 btbl Sbtbl ->
      j_cond_sem d (G0++G) c Sc ->
      j_tml_sem (G0++G) (tmlist_of_ctx G0) Stml ->
      s0 = List.concat G0 ->
      j_q_sem d G s0 (selstar b btbl c) 
        (fun h => let S1 := Sbtbl h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Evl.env_app _ _ (Evl.env_of_tuple G0 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml (Evl.env_app _ _ (Evl.env_of_tuple G0 Vl) h) in
                  let S := cast _ _ e (Rel.sum S2 f)
                  in if b then Rel.flat S else S)
  | jqs_union : forall G b q1 q2,
      forall s S1 S2,
      j_q_sem d G s q1 S1 -> j_q_sem d G s q2 S2 ->
      j_q_sem d G s (qunion b q1 q2) 
        (fun Vl => let S := Rel.plus (S1 Vl) (S2 Vl) in if b then S else Rel.flat S)
  | jqs_inters : forall G b q1 q2,
      forall s S1 S2,
      j_q_sem d G s q1 S1 -> j_q_sem d G s q2 S2 ->
      j_q_sem d G s (qinters b q1 q2) 
        (fun Vl => let S := Rel.inter (S1 Vl) (S2 Vl) in if b then S else Rel.flat S)
  | jqs_except : forall G b q1 q2,
      forall s S1 S2,
      j_q_sem d G s q1 S1 -> j_q_sem d G s q2 S2 ->
      j_q_sem d G s (qexcept b q1 q2) 
        (fun Vl => if b then Rel.minus (S1 Vl) (S2 Vl) else Rel.minus (Rel.flat (S1 Vl)) (S2 Vl))
  with j_tb_sem (d : Db.D) : forall G (s : Scm), pretb -> (env G -> Rel.R (List.length s)) -> Prop :=
  | jtbs_base : forall G x,
      forall s (e : Db.db_schema d x = Some s), 
      j_tb_sem d G s (tbbase x) (fun _ => Db.db_rel e)
  | jtbs_query : forall G q,
      forall s h,
      j_q_sem d G s q h ->
      j_tb_sem d G s (tbquery q) h
  with j_cond_sem (d : Db.D) : forall G, precond -> (env G -> B) -> Prop :=
  | jcs_true : forall G, j_cond_sem d G cndtrue (fun _ => btrue)
  | jcs_false : forall G, j_cond_sem d G cndfalse (fun _ => bfalse)
  | jcs_null : forall G b t, 
      forall St,
      j_tm_sem G t St ->
      j_cond_sem d G (cndnull b t) (fun Vl => of_bool (match St Vl with None => b | _ => negb b end))
  | jcs_pred : forall G n p tml,
      forall Stml e,
      j_tml_sem G tml Stml ->
      j_cond_sem d G (cndpred n p tml) (fun Vl => Sem.sem_bpred _ p (to_list (Stml Vl)) (eq_trans (length_to_list _ _ _) e))
  | jcs_memb : forall G b tml q, 
      forall s Stml Sq (e : length tml = length s), (* Rel.T (length tml) = t Value (length s)) *)
      j_tml_sem G tml Stml ->
      j_q_sem d G s q Sq ->
      let e' := f_equal Rel.T e in 
      j_cond_sem d G (cndmemb b tml q) (fun Vl => 
        let Stt := Rel.sel (Sq Vl) (fun rl => Vector.fold_right2 (fun r0 V0 acc => acc && is_btrue (veq r0 V0))%bool true _ rl (cast _ _ e' (Stml Vl))) in
        let Suu := Rel.sel (Sq Vl) (fun rl => Vector.fold_right2 (fun r0 V0 acc => acc && negb (is_bfalse (veq r0 V0)))%bool true _ rl (cast _ _ e' (Stml Vl))) in
        let ntt := Rel.card Stt in
        let nuu := Rel.card Suu in
        if (0 <? ntt) then of_bool b
        else if (0 <? nuu) then bmaybe
        else of_bool (negb b))
  | jcs_ex : forall G q,
      forall Sq,
      j_in_q_sem d G q Sq ->
      j_cond_sem d G (cndex q) (fun Vl => of_bool (Sq Vl))
  | jcs_and : forall G c1 c2,
      forall Sc1 Sc2,
      j_cond_sem d G c1 Sc1 -> j_cond_sem d G c2 Sc2 ->
      j_cond_sem d G (cndand c1 c2) (fun Vl => band (Sc1 Vl) (Sc2 Vl))
  | jcs_or : forall G c1 c2,
      forall Sc1 Sc2,
      j_cond_sem d G c1 Sc1 -> j_cond_sem d G c2 Sc2 ->
      j_cond_sem d G (cndor c1 c2) (fun Vl => bor (Sc1 Vl) (Sc2 Vl))
  | jcs_not : forall G c0,
      forall Sc0,
      j_cond_sem d G c0 Sc0 ->
      j_cond_sem d G (cndnot c0) (fun Vl => bneg (Sc0 Vl))
  with j_btb_sem (d : Db.D) : forall G G', list (pretb * Scm) -> (env G -> Rel.R (list_sum (List.map (length (A:=Name)) G'))) -> Prop :=
  | jbtbs_nil : forall G, j_btb_sem d G List.nil List.nil (fun _ => Rel.Rone) 
  | jbtbs_cons : forall G T s' btb,
      forall s G0 ST Sbtb e,
      j_tb_sem d G s T ST ->
      j_btb_sem d G G0 btb Sbtb -> length s = length s' ->
      j_btb_sem d G (s'::G0) ((T,s')::btb) (fun Vl => cast _ _ e (Rel.times (ST Vl) (Sbtb Vl)))
  with j_btbl_sem (d : Db.D) : forall G G', list (list (pretb * Scm)) -> (env G -> Rel.R (list_sum (List.map (length (A:=Name)) G'))) -> Prop :=
  | jbtbls_nil : forall G, j_btbl_sem d G List.nil List.nil (fun _ => Rel.Rone) 
  | jbtbls_cons : forall G btb btbl,
      forall G0 G1 Sbtb Sbtbl e,
      j_btb_sem d G G0 btb Sbtb ->
      j_btbl_sem d (G0 ++ G) G1 btbl Sbtbl ->
      j_btbl_sem d G (G1 ++ G0) (btb::btbl)
        (fun h =>
         let Rbtb := Sbtb h in
         R_sum Rbtb (fun Vl => cast _ _ e (Rel.times (R_single Vl) (Sbtbl (Evl.env_app _ _ (Evl.env_of_tuple _ Vl) h)))))
(*         let Rbtbl := Sbtbl h in
         R_sum Rbtbl (fun Vl => cast _ _ e (Rel.times (Sbtb (Evl.env_app _  _ (Evl.env_of_tuple _ Vl) h)) (R_single Vl))))
*)
  with j_in_q_sem (d : Db.D) : forall G, prequery -> (env G -> bool) -> Prop :=
  | jiqs_sel : forall G b tml btbl c,
      forall G0 Sbtbl Sc Stml,
      j_btbl_sem d G G0 btbl Sbtbl ->
      j_cond_sem d (G0++G) c Sc ->
      j_tml_sem (G0++G) (List.map fst tml) Stml ->
      j_in_q_sem d G (select b tml btbl c) 
        (fun h => let S1 := Sbtbl h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Evl.env_app _ _ (Evl.env_of_tuple G0 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml (Evl.env_app _ _ (Evl.env_of_tuple G0 Vl) h) in
                  let S := Rel.sum S2 f
                  in 0 <? Rel.card (if b then Rel.flat S else S))
  | jiqs_selstar : forall G b btbl c,
      forall G0 Sbtbl Sc,
      j_btbl_sem d G G0 btbl Sbtbl ->
      j_cond_sem d (G0++G) c Sc ->
      j_in_q_sem d G (selstar b btbl c) 
        (fun h => let S1 := Sbtbl h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Evl.env_app _ _ (Evl.env_of_tuple G0 Vl) h)) in
                  let S2 := Rel.sel S1 p in
(*                  let f  := fun _ => Vector.nil Rel.V) in
                  let S := cast _ _ e (Rel.sum S2 f) 
                  in if b then Rel.flat S else S)
no, we can simplify *)
                  0 <? Rel.card S2)
  | jiqs_union : forall G b q1 q2,
      forall s S1 S2,
      j_q_sem d G s q1 S1 -> j_q_sem d G s q2 S2 ->
      j_in_q_sem d G (qunion b q1 q2) 
        (fun Vl => let S := Rel.plus (S1 Vl) (S2 Vl) in 0 <? Rel.card (if b then S else Rel.flat S))
  | jiqs_inters : forall G b q1 q2,
      forall s S1 S2,
      j_q_sem d G s q1 S1 -> j_q_sem d G s q2 S2 ->
      j_in_q_sem d G (qinters b q1 q2) 
        (fun Vl => let S := Rel.inter (S1 Vl) (S2 Vl) in 0 <? Rel.card (if b then S else Rel.flat S))
  | jiqs_except : forall G b q1 q2,
      forall s S1 S2,
      j_q_sem d G s q1 S1 -> j_q_sem d G s q2 S2 ->
      j_in_q_sem d G (qexcept b q1 q2) 
        (fun Vl => 0 <? Rel.card (if b then Rel.minus (S1 Vl) (S2 Vl) else Rel.minus (Rel.flat (S1 Vl)) (S2 Vl)))
  .

  Scheme jqs_ind_mut := Induction for j_q_sem Sort Prop
  with jTs_ind_mut := Induction for j_tb_sem Sort Prop
  with jcs_ind_mut := Induction for j_cond_sem Sort Prop
  with jbTs_ind_mut := Induction for j_btb_sem Sort Prop
  with jbTls_ind_mut := Induction for j_btbl_sem Sort Prop
  with jiqs_ind_mut := Induction for j_in_q_sem Sort Prop.

  Combined Scheme j_sem_ind_mut from jqs_ind_mut, jTs_ind_mut, jcs_ind_mut, jbTs_ind_mut, jbTls_ind_mut, jiqs_ind_mut.


  Derive Inversion j_q_sel_sem with (forall d G s b tml btb c Ssel, j_q_sem d G s (select b tml btb c) Ssel) Sort Prop.
  Derive Inversion j_q_selstar_sem with (forall d G s b btb c Sss, j_q_sem d G s (selstar b btb c) Sss) Sort Prop.
  Derive Inversion j_q_union_sem with (forall d G s b q1 q2 Sq, j_q_sem d G s (qunion b q1 q2) Sq) Sort Prop.
  Derive Inversion j_q_inters_sem with (forall d G s b q1 q2 Sq, j_q_sem d G s (qinters b q1 q2) Sq) Sort Prop.
  Derive Inversion j_q_except_sem with (forall d G s b q1 q2 Sq, j_q_sem d G s (qexcept b q1 q2) Sq) Sort Prop.
  Derive Inversion j_tb_base_sem with (forall d G s x ST, j_tb_sem d G s (tbbase x) ST) Sort Prop.
  Derive Inversion j_tb_query_sem with (forall d G s q ST, j_tb_sem d G s (tbquery q) ST) Sort Prop.
  Derive Inversion j_cons_btb_sem with (forall d G G' T s tl Scons, j_btb_sem d G G' ((T,s)::tl) Scons) Sort Prop.
  Derive Inversion j_cons_btbl_sem with (forall d G G' btb btbl Scons, j_btbl_sem d G G' (btb::btbl) Scons) Sort Prop.
  Derive Inversion j_iq_sel_sem with (forall d G b tml btb c Ssel, j_in_q_sem d G (select b tml btb c) Ssel) Sort Prop.
  Derive Inversion j_iq_selstar_sem with (forall d G b btb c Sss, j_in_q_sem d G (selstar b btb c) Sss) Sort Prop.
  Derive Inversion j_iq_union_sem with (forall d G b q1 q2 Sq, j_in_q_sem d G (qunion b q1 q2) Sq) Sort Prop.
  Derive Inversion j_iq_inters_sem with (forall d G b q1 q2 Sq, j_in_q_sem d G (qinters b q1 q2) Sq) Sort Prop.
  Derive Inversion j_iq_except_sem with (forall d G b q1 q2 Sq, j_in_q_sem d G (qexcept b q1 q2) Sq) Sort Prop.

  Lemma j_nil_btb_sem :
    forall d G G' Snil (P : Prop),
       (forall (G0 G0': Ctx), G0 = G -> G0' = G' -> List.nil = G0' ->
        (fun (_:Evl.env G) => Rel.Rone) ~= Snil -> P) ->
       j_btb_sem d G G' List.nil Snil -> P.
  Proof.
    intros.
    enough (forall G0 G0' (btb0 : list (pretb * Scm)) 
      (Snil0 : Evl.env G0 -> Rel.R (list_sum (List.map (length (A:=Name)) G0'))), 
        j_btb_sem d G0 G0' btb0 Snil0 ->
        G0 = G -> G0' = G' -> List.nil = btb0 -> Snil0 ~= Snil -> P).
    apply (H1 _ _ _ _ H0 eq_refl eq_refl eq_refl JMeq_refl).
    intros G0 G0' btb0 Snil0 H0'.
    destruct H0'; intros. eapply H; auto. rewrite H1 in H4. exact H4.
    discriminate H5.
  Qed.

  Lemma j_nil_btbl_sem :
    forall d G G' Snil (P : Prop),
       (forall (G0 G0': Ctx), G0 = G -> G0' = G' -> List.nil = G0' ->
        (fun (_:Evl.env G) => Rel.Rone) ~= Snil -> P) ->
       j_btbl_sem d G G' List.nil Snil -> P.
  Proof.
    intros.
    enough (forall G0 G0' btbl0
      (Snil0 : Evl.env G0 -> Rel.R (list_sum (List.map (length (A:=Name)) G0'))), 
        j_btbl_sem d G0 G0' btbl0 Snil0 ->
        G0 = G -> G0' = G' -> List.nil = btbl0 -> Snil0 ~= Snil -> P).
    apply (H1 _ _ _ _ H0 eq_refl eq_refl eq_refl JMeq_refl).
    intros G0 G0' btbl0 Snil0 H0'.
    destruct H0'; intros. eapply H; auto. rewrite H1 in H4. exact H4.
    discriminate H4.
  Qed.

  Theorem j_sem_fun : forall d,
    (forall G s q Sq, j_q_sem d G s q Sq -> forall s0 Sq0, j_q_sem d G s0 q Sq0 -> s = s0 /\ Sq ~= Sq0) /\
    (forall G s T ST, j_tb_sem d G s T ST -> forall s0 ST0, j_tb_sem d G s0 T ST0 -> s = s0 /\ ST ~= ST0) /\
    (forall G c Sc, j_cond_sem d G c Sc -> forall Sc0, j_cond_sem d G c Sc0 -> Sc ~= Sc0) /\
    (forall G G' btb Sbtb, j_btb_sem d G G' btb Sbtb -> 
      forall G0' Sbtb0, j_btb_sem d G G0' btb Sbtb0 -> G' = G0' /\ Sbtb ~= Sbtb0) /\
    (forall G G' btbl Sbtbl, j_btbl_sem d G G' btbl Sbtbl -> 
      forall G0' Sbtbl0, j_btbl_sem d G G0' btbl Sbtbl0 -> G' = G0' /\ Sbtbl ~= Sbtbl0) /\
    (forall G q Sq, j_in_q_sem d G q Sq -> forall Sq0, j_in_q_sem d G q Sq0 -> Sq ~= Sq0).
  Proof.
    intro. apply j_sem_ind_mut.
    (* query *)
    + intros.
      (* the Coq refiner generates an ill-typed term if we don't give enough parameters to this eapply *)
      eapply (j_q_sel_sem _ _ _ _ _ _ _ _ (fun _ _ s1 _ _ _ _ Ssel =>
        _ = s1 /\ (fun h =>
        let S1 := Sbtbl h in
        let p := fun Vl => is_btrue (Sc (Evl.env_app G0 G (Evl.env_of_tuple G0 Vl) h)) in
        let S2 := Rel.sel S1 p in
        let f := fun Vl => Stml (Evl.env_app G0 G (Evl.env_of_tuple G0 Vl) h) in
        let S := cast _ _ e (Rel.sum S2 f) in
        if b then Rel.flat S else S) ~= Ssel) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H13); clear H13; intros; subst.
      clear H3. apply (existT_eq_elim (JMeq_eq H4)); clear H4; intros; subst.
      clear H3. destruct (H _ _ H7); subst. pose (H11 := H0 _ H8); clearbody H11. 
      rewrite H4.
      rewrite H11.
      replace e1 with e. replace Stml0 with Stml.
      split; reflexivity. apply (j_tml_sem_fun _ _ _ j1 _ H9). apply UIP.
    + intros. eapply (j_q_selstar_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H12); clear H12; intros; subst.
      clear H3. apply (existT_eq_elim (JMeq_eq H4)); clear H4; intros; subst.
      clear H3. destruct (H _ _ H6); subst. pose (H10 := H0 _ H7); clearbody H10. 
      rewrite H4, H10. replace e1 with e. replace Stml0 with Stml.
      split; reflexivity. apply (j_tml_sem_fun _ _ _ j1 _ H8). apply UIP.
    + intros. eapply (j_q_union_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H10); clear H10; intros; subst.
      clear H3 H2. apply (existT_eq_elim (JMeq_eq H5)); clear H5; intros; subst.
      clear H2. destruct (H _ _ H4); subst. destruct (H0 _ _ H7); subst. intuition.
    + intros. eapply (j_q_inters_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H10); clear H10; intros; subst.
      clear H3 H2. apply (existT_eq_elim (JMeq_eq H5)); clear H5; intros; subst.
      clear H2. destruct (H _ _ H4); subst. destruct (H0 _ _ H7); subst. intuition.
    + intros. eapply (j_q_except_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H10); clear H10; intros; subst.
      clear H3 H2. apply (existT_eq_elim (JMeq_eq H5)); clear H5; intros; subst.
      clear H2. destruct (H _ _ H4); subst. destruct (H0 _ _ H7); subst. intuition.
    (* table *)
    + intros. eapply (j_tb_base_sem _ _ _ _ _ (fun _ _ _ _ _ => _) _ H). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H4); clear H4; intros; subst.
      clear H1. apply (existT_eq_elim (JMeq_eq H2)); clear H2; intros; subst.
      clear H H0 H1. generalize e, e0. rewrite e in e0. injection e0. intuition.
      generalize e1. rewrite H. intro.
      replace e3 with e2. reflexivity. apply UIP.
    + intros. eapply (j_tb_query_sem _ _ _ _ _ (fun _ _ _ _ _ => _) _ H0). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H6); clear H6; intros; subst.
      clear H2. apply (existT_eq_elim (JMeq_eq H3)); clear H3; intros; subst.
      clear H1 H2. destruct (H _ _ H4); subst. intuition.
    (* cond *)
    + intros. inversion H. reflexivity.
    + intros. inversion H. reflexivity.
    + intros. inversion H. apply (existT_eq_elim H4); clear H4; intros; subst.
      replace St0 with St. reflexivity. apply (j_tm_sem_fun _ _ _ j _ H2).
    + intros. inversion H. apply (existT_eq_elim H3); clear H3; intros; subst.
      apply (existT_eq_elim H5); clear H5; intros; subst. 
      replace e0 with (@eq_refl _ (length tml)).
      replace Stml0 with Stml. reflexivity.
      apply (j_tml_sem_fun _ _ _ j _ H2). apply UIP.
    + intros. inversion H0. apply (existT_eq_elim H6); clear H6; intros; subst. clear H6.
      destruct (H _ _ H7). subst. rewrite H2.
      replace Stml0 with Stml. replace e'0 with e'. reflexivity.
      apply UIP. apply (j_tml_sem_fun _ _ _ j _ H4).
    + intros. inversion H0. apply (existT_eq_elim H3); clear H3; intros; subst. clear H3.
      rewrite (H _ H4). reflexivity.
    + intros. inversion H1. apply (existT_eq_elim H5); clear H5; intros; subst.
      rewrite (H _ H6). rewrite (H0 _ H7). reflexivity.
    + intros. inversion H1. apply (existT_eq_elim H5); clear H5; intros; subst.
      rewrite (H _ H6). rewrite (H0 _ H7). reflexivity.
    + intros. inversion H0. apply (existT_eq_elim H3); clear H3; intros; subst.
      rewrite (H _ H4). reflexivity.
    (* btb *)
    + intros. eapply (j_nil_btb_sem _ _ _ _ _ _ H). Unshelve.
      intros; simpl; subst. intuition.
    + intros. eapply (j_cons_btb_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _  => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H12); clear H12; intros; subst.
      clear H11 H3. apply (existT_eq_elim (JMeq_eq H4)); clear H4; intros; subst.
      clear H3. destruct (H _ _ H6); subst. destruct (H0 _ _ H8); subst. intuition.
      rewrite H5. replace e with e1. reflexivity. apply UIP.
    (* btbl *)
    + intros. eapply (j_nil_btbl_sem _ _ _ _ _ _ H). Unshelve. simpl.
      intros; simpl; subst. intuition.
    + intros. eapply (j_cons_btbl_sem _ _ _ _ _ _ (fun _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H10); clear H10; intros; subst.
      clear H9 H3. apply (existT_eq_elim (JMeq_eq H4)); clear H4; intros.
      destruct (H _ _ H5); subst. destruct (H0 _ _ H7); subst; intuition.
      clear H3. rewrite H6. replace e with e0. reflexivity. apply UIP.
    (* inner query *)
    + intros. eapply (j_iq_sel_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ Ssel =>
        (fun h =>
         let S1 := Sbtbl h in
         let p := fun Vl => is_btrue (Sc (Evl.env_app G0 G (Evl.env_of_tuple G0 Vl) h)) in
         let S2 := Rel.sel S1 p in
         let f := fun Vl => Stml (Evl.env_app G0 G (Evl.env_of_tuple G0 Vl) h) in
         let S := Rel.sum S2 f in 
         0 <? Rel.card (if b then Rel.flat S else S)) ~= Ssel) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H11); clear H11; intros; subst.
      clear H2 H3. destruct (H _ _ H4); subst. pose (H9 := H0 _ H7); clearbody H9. 
      rewrite H3, H9. replace Stml0 with Stml. reflexivity.
      apply (j_tml_sem_fun _ _ _ j1 _ H8).
    + intros. eapply (j_iq_selstar_sem _ _ _ _ _ _ (fun _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H9); clear H9; intros; subst.
      clear H2 H4. destruct (H _ _ H3); subst. pose (H7 := H0 _ H6); clearbody H7. 
      rewrite H4, H7. reflexivity.
    + intros. eapply (j_iq_union_sem _ _ _ _ _ _ (fun _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H9); clear H9; intros; subst.
      clear H2 H4. destruct (H _ _ H3); subst. destruct (H0 _ _ H6); subst. intuition.
    + intros. eapply (j_iq_inters_sem _ _ _ _ _ _ (fun _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H9); clear H9; intros; subst.
      clear H2 H4. destruct (H _ _ H3); subst. destruct (H0 _ _ H6); subst. intuition.
    + intros. eapply (j_iq_except_sem _ _ _ _ _ _ (fun _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H9); clear H9; intros; subst.
      clear H2 H4. destruct (H _ _ H3); subst. destruct (H0 _ _ H6); subst. intuition.
  Qed.

  Theorem j_sem_fun_dep : forall d,
    (forall G s q Sq, j_q_sem d G s q Sq -> 
      forall G0 s0 q0 Sq0, G = G0 -> q = q0 -> j_q_sem d G0 s0 q0 Sq0 -> s = s0 /\ Sq ~= Sq0) /\
    (forall G s T ST, j_tb_sem d G s T ST -> 
      forall G0 s0 T0 ST0, G = G0 -> T = T0 -> j_tb_sem d G0 s0 T0 ST0 -> s = s0 /\ ST ~= ST0) /\
    (forall G c Sc, j_cond_sem d G c Sc -> 
      forall G0 c0 Sc0, G = G0 -> c = c0 -> j_cond_sem d G0 c0 Sc0 -> Sc ~= Sc0) /\
    (forall G G' btb Sbtb, j_btb_sem d G G' btb Sbtb -> 
      forall G0 G0' btb0 Sbtb0, G = G0 -> btb = btb0 -> j_btb_sem d G0 G0' btb0 Sbtb0 -> 
      G' = G0' /\ Sbtb ~= Sbtb0) /\
    (forall G G' btbl Sbtbl, j_btbl_sem d G G' btbl Sbtbl -> 
      forall G0 G0' btbl0 Sbtbl0, G = G0 -> btbl = btbl0 -> j_btbl_sem d G0 G0' btbl0 Sbtbl0 -> 
      G' = G0' /\ Sbtbl ~= Sbtbl0) /\
    (forall G q Sq, j_in_q_sem d G q Sq -> 
      forall G0 q0 Sq0, G = G0 -> q = q0 -> j_in_q_sem d G0 q0 Sq0 -> Sq ~= Sq0).
  Proof.
    intro. decompose [and] (j_sem_fun d). split.
      intros. subst. apply (H _ _ _ _ H4 _ _ H8).
    split.
      intros. subst. apply (H1 _ _ _ _ H4 _ _ H8).
    split.
      intros. subst. apply (H0 _ _ _ H4 _ H8).
    split.
      intros. subst. apply (H2 _ _ _ _ H4 _ _ H8).
    split.
      intros. subst. apply (H3 _ _ _ _ H4 _ _ H8).
    intros. subst. apply (H5 _ _ _ H4 _ H8).
  Qed.

  Corollary jT_sem_fun_dep : forall d G s T ST, j_tb_sem d G s T ST -> 
      forall G0 s0 T0 ST0, G = G0 -> T = T0 -> j_tb_sem d G0 s0 T0 ST0 -> s = s0 /\ ST ~= ST0.
  Proof.
    intro. decompose [and] (j_sem_fun_dep d). exact H1.
  Qed.

  Corollary jq_sem_fun_dep : forall d G s q Sq, j_q_sem d G s q Sq -> 
      forall G0 s0 q0 Sq0, G = G0 -> q = q0 -> j_q_sem d G0 s0 q0 Sq0 -> s = s0 /\ Sq ~= Sq0.
  Proof.
    intro. decompose [and] (j_sem_fun_dep d). exact H.
  Qed.

  Corollary jc_sem_fun_dep : forall d G c Sc, j_cond_sem d G c Sc -> 
      forall G0 c0 Sc0, G = G0 -> c = c0 -> j_cond_sem d G0 c0 Sc0 -> Sc ~= Sc0.
  Proof.
    intro. decompose [and] (j_sem_fun_dep d). exact H0.
  Qed.

(* XXX: will be moved to auxiliary file *)
  Lemma eq_rect_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect x P p x eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_rect_r_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect_r P p eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
  rewrite H. reflexivity.
  Qed.

End SQLSemantics.