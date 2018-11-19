Require Import Eqdep Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool 
  Semantics JMeq FunctionalExtensionality Omega Coq.Init.Specif ProofIrrelevance.

Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

Axiom UIP : forall A (a : A) (e : a = a), e = eq_refl. 
  Lemma eq_rect_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect x P p x eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_rect_r_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect_r P p eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
  rewrite H. reflexivity.
  Qed.

  Definition unopt {A} : forall (x : option A), x <> None -> A.
    refine (fun x => match x as x0 return (x0 <> None -> A) with Some x' => fun _ => x' | None => _ end).
    intro Hfalse. contradiction Hfalse. reflexivity.
  Defined.

  Definition nth_lt {A} : forall (l : list A) n, n < length l -> A.
    refine (fun l n Hn => unopt (nth_error l n) _). apply nth_error_Some. exact Hn.
  Defined.

Module Translation2V (Db : DB) (Sql : SQL Db).
  Import Db.
  Import Sql.

  Module S2 := Sem2 Db.
  Module S3 := Sem3 Db.
  Module Ev := Evl Db Sql.
  Module SQLSem2 := SQLSemantics Db S2 Sql Ev.
  Module SQLSem3 := SQLSemantics Db S3 Sql Ev.

  (* just some trivial operations on names *)
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
          cndnot (cndex (selstar false (List.cons (tbquery (ttquery d Q), al) List.nil)
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
          cndnot (cndex (selstar false (List.cons (tbquery (ttquery d Q), al) List.nil)
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
    | select b btm btb c => select b btm (List.map (fun bt => (tttable d (fst bt), snd bt)) btb) (ttcond d c)
    | selstar b btb c => selstar b (List.map (fun bt => (tttable d (fst bt), snd bt)) btb) (ttcond d c)
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

  Lemma p_ext' : 
    forall m n, forall e : m = n, forall r : Rel.R m, forall s : Rel.R n, 
      (forall t, Rel.memb r t = Rel.memb s (eq_rect _ _ t _ e)) -> r ~= s.
  intros m n e. rewrite e. simpl.
  intros. rewrite (Rel.p_ext n r s). constructor. exact H.
  Qed.

  Lemma j_select_inv :
    forall d g b btm btb c s, forall P : (forall g0 q0 s0, j_query d g0 q0 s0 -> Prop),
    (forall g1 H, forall Hbtb : j_btb d g btb g1, forall Hc : j_cond d (g1 ++ g) c,
     forall Html : j_tml (g1 ++ g) (List.map fst btm), forall Hs : s = List.map snd btm,
       H = j_select _ _ _ _ _ _ _ _ Hbtb Hc Html Hs -> P g (select b btm btb c) s H) ->
    forall H : j_query d g (select b btm btb c) s,
    P g (select b btm btb c) s H.
  intros d g b btm btb c s P Hinv H. dependent inversion H.
  eapply Hinv. trivial.
  Qed.

(*
  Lemma sem3_pred_ttrue : forall d G n p tml Hdb Html e h,
    SQLSem3.cond_sem d G (cndpred n p tml) (j_cndpred d G n p tml Hdb Html e) h = ttrue -> 
    exists vl Hvl, monadic_map (fun val => val) (Ev.tml_sem G tml Html h) = Some vl /\ p vl Hvl = true.
  simpl. intros d G n p tml Hdb Html e h. destruct e.
  repeat rewrite eq_rect_eq_refl. repeat rewrite eq_rect_r_eq_refl.
  apply S3.sem_bpred_elim.
  - intros cl e0 Hcl Hp. exists cl. exists Hcl. split. rewrite e0. reflexivity.
    destruct (p cl Hcl) eqn:e1; auto; simpl in Hp; discriminate Hp.
  - intros _ Hfalse. discriminate Hfalse.
  Qed.

  Lemma sem3_pred_tfalse : forall d G n p tml Hdb Html e h,
    SQLSem3.cond_sem d G (cndpred n p tml) (j_cndpred d G n p tml Hdb Html e) h = tfalse -> 
    exists vl Hvl, monadic_map (fun val => val) (Ev.tml_sem G tml Html h) = Some vl /\ p vl Hvl = false.
  simpl. intros d G n p tv Hdb Html e h. destruct e. 
  repeat rewrite eq_rect_eq_refl. repeat rewrite eq_rect_r_eq_refl.
  apply S3.sem_bpred_elim.
  - intros cl e0 Hcl Hp. exists cl. exists Hcl. split. rewrite e0. reflexivity.
    destruct (p cl Hcl) eqn:e1; auto; simpl in Hp; discriminate Hp.
  - intros _ Hfalse. discriminate Hfalse.
  Qed.

  Lemma sem3_pred_unknown : forall d G n p tml Hdb Html e h,
    SQLSem3.cond_sem d G (cndpred n p tml) (j_cndpred d G n p tml Hdb Html e) h = unknown ->
    monadic_map (fun val => val) (Ev.tml_sem G tml Html h) = @None (list BaseConst).
  simpl. intros d G n p tv Hdb Html e h. destruct e. 
  repeat rewrite eq_rect_eq_refl. repeat rewrite eq_rect_r_eq_refl.
  apply S3.sem_bpred_elim.
  + intros cl e0 Hcl. destruct (p cl Hcl); simpl; intro Hfalse; discriminate Hfalse.
  + intros H _. exact H.
  Qed.
*)

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

(*
  Lemma sem2_pred_false_aux (d : D) (g : Ctx) tml :
    forall Hc Html h, monadic_map (fun val => val) (Ev.tml_sem g tml Html h) = @None (list BaseConst) ->
    SQLSem2.cond_sem d g
     (List.fold_right (fun (t : pretm) (acc : precond) => (t IS NOT NULL) AND acc) (TRUE) tml) Hc h = false.
  Proof.
    intros Hc Html h Hmap.
    cut (forall t0 Ht0 tml0, Ev.tm_sem g t0 Ht0 h = None -> List.In t0 tml0 -> 
      forall Hc0, SQLSem2.cond_sem d g (List.fold_right (fun t1 acc => (t1 IS NOT NULL) AND acc) (TRUE) tml0) Hc0 h = false).
    + intro Hcut. cut (exists t, exists (Hin : List.In t tml), Ev.tm_sem g t (Html _ Hin) h = None).
      - intro H. decompose record H. apply (Hcut _ _ _ H1 x0).
      - generalize Html, Hmap. clear Html Hmap Hcut. elim tml.
        * simpl. unfold ret. intros Html Hfalse. discriminate Hfalse.
        * intros hd tl IH Html. simpl. 
          destruct (monadic_map (fun val => val) (Ev.tml_sem g tl (fun t Ht => Html t (or_intror Ht)) h)) eqn:e.
          ++ simpl. 
             assert (forall x, x = Ev.tm_sem g hd (Html hd (or_introl eq_refl)) h -> 
                      bind x (fun b : BaseConst => ret (b :: l)) = None ->
                      exists (t : pretm) (Hin : hd = t \/ List.In t tl), Ev.tm_sem g t (Html t Hin) h = None).
            -- intro x. destruct x.
              ** simpl. unfold ret. intros _ Hfalse. discriminate Hfalse.
              ** simpl. intros. exists hd. eexists. rewrite H. reflexivity.
            -- apply H. reflexivity.
        ++ intros _. destruct (IH _ e). destruct H. exists x. eexists. exact H.
    + intros t0 Ht0 tml0 Hnone. generalize h, Hnone. clear h Hmap Hnone. elim tml0.
      - simpl. intros h Hnone Hfalse. contradiction Hfalse.
      - simpl. intros t1 tml1 IH h Hnone Hin Hc0.
        generalize h, Ht0, Hnone. clear h Hnone.
        dependent inversion Hc0 with (fun G0 c1 Hinv => forall h Ht0, Ev.tm_sem G0 t0 Ht0 h = None ->
            SQLSem2.cond_sem d G0 c1 Hinv h = false).
        intros. simpl. repeat rewrite eq_rect_r_eq_refl. destruct Hin.
        * replace (SQLSem2.cond_sem d g (t1 IS NOT NULL) j h) with false. reflexivity.
          generalize h Ht1 H0. clear h Ht1 H0.
          dependent inversion j with (fun G1 c3 Hinv => 
            forall h Ht1, Ev.tm_sem G1 t0 Ht1 h = None -> false = SQLSem2.cond_sem d G1 c3 Hinv h).
          rewrite <- H3. intros. simpl. repeat rewrite eq_rect_r_eq_refl.
          rewrite <- (Ev.tm_sem_pi g t1 Ht1 h j2); auto. rewrite H4. reflexivity.
        * replace (SQLSem2.cond_sem d g (List.fold_right (fun t2 acc => (t2 IS NOT NULL) AND acc) (TRUE) tml1) j0 h) with false. 
          apply Bool.andb_false_intro2. reflexivity.
          symmetry. apply IH. rewrite <- H0. apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
          exact H3.
  Qed.

  Lemma sem2_pred_true_aux (d : D) (g : Ctx) tml Hc Html x h:
    monadic_map (fun val => val) (Ev.tml_sem g tml Html h) = Some x ->
    SQLSem2.cond_sem d g
     (List.fold_right (fun (t : pretm) (acc : precond) => (t IS NOT NULL) AND acc) (TRUE) tml) Hc h = true.
  Proof.
    intro Hmap.
    enough (forall t0 Ht0, List.In t0 tml -> exists v, Ev.tm_sem g t0 Ht0 h = Some v).
    + generalize Hc H. clear H Hmap Html Hc. elim tml; simpl; intros.
      - cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d g (TRUE) Hc h0 = true).
        * intro H'. apply H'. reflexivity.
        * dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h -> SQLSem2.cond_sem d G0 c0 Hinv h0 = true).
          intros. constructor.
      - cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d g ((a IS NOT NULL) AND List.fold_right (fun (t : pretm) (acc : precond) => 
              (t IS NOT NULL) AND acc) (TRUE) l) Hc h0 = true).
        * intro H'. apply H'. reflexivity.
        * dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h -> SQLSem2.cond_sem d G0 c0 Hinv h0 = true).
          intros. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite H2. clear H2 h0.
          apply S2_is_btrue_and_intro.
          ++ cut (forall h0, h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d g (a IS NOT NULL) j h0) = true).
            -- intro H'. apply H'. reflexivity.
            -- dependent inversion j with (fun G0 c0 Hinv => forall h0, h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d G0 c0 Hinv h0) = true).
              intros. simpl. repeat rewrite eq_rect_r_eq_refl.
              destruct (H0 _ j2 (or_introl eq_refl)). rewrite H5. rewrite H8. reflexivity.
          ++ apply H. intros. apply H0. right. exact H2.
    + generalize x Html Hmap; clear x Html Hmap. elim tml; simpl; intros.
      - contradiction H.
      - destruct H0.
        * destruct (monadic_map (fun val => val) (Ev.tml_sem g l (fun t H => Html t (or_intror H)) h)) in Hmap; simpl in Hmap. Focus 2. discriminate Hmap.
          destruct (Ev.tm_sem g a (Html a (@or_introl _ (List.In a l) eq_refl)) h) eqn:e; simpl in Hmap. Focus 2. discriminate Hmap.
          generalize Ht0. clear Ht0. rewrite <- H0. intro Ha. exists b. rewrite <- e.
          apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
        * assert (j_tml g l). intros t1 Ht1. apply Html. right. exact Ht1.
          destruct (monadic_map (fun val => val) (Ev.tml_sem g l (fun t H => Html t (or_intror H)) h)) eqn:e; simpl in Hmap. Focus 2. discriminate Hmap.
          apply (H l0 X). Focus 2. exact H0. rewrite <- e.
          f_equal. apply JMeq_eq. apply Ev.tml_sem_pi. reflexivity.
  Qed.
*)

  Theorem j_query_j_db : forall d G Q s, j_query d G Q s -> j_db d.
  intros d G Q s HWF.
  eapply (jq_ind_mut _ 
          (fun G0 Q0 s0 H0 => j_db d)
          (fun G0 T0 s0 H0 => j_db d)
          (fun G0 c0 H0 => j_db d)
          (fun G0 btb G1 H0 => j_db d) 
          (fun G0 Q0 H0 => j_db d)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF).
  Unshelve. all: simpl; intros; auto.
  Qed.

(*
  Lemma fold_v_tml_sem1 g tml Html h :
           (fun rl => fold_right2 (fun r0 V0 acc => 
              acc && S2.is_btrue (S2.veq r0 V0))%bool true (length tml) rl (Ev.v_tml_sem g tml Html h))
           = (fun rl => fold_right2 (fun r0 V0 acc => 
              acc && S3.is_btrue (S3.veq r0 V0))%bool true (length tml) rl (Ev.v_tml_sem g tml Html h)).
  Proof.
    extensionality rl.
    eapply (Vector.rect2 (fun n rl0 tml0 => 
      (fold_right2 (fun (r0 V0 : option BaseConst) (acc : bool) => (acc && S2.is_btrue (S2.veq r0 V0))%bool) true n rl0 tml0 =
       fold_right2 (fun (r0 V0 : option BaseConst) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true n rl0 tml0)) 
      _ _ rl (Ev.v_tml_sem g tml Html h)). Unshelve.
    + reflexivity.
    + intros n v1 v2 IH x1 x2. simpl. f_equal.
      - apply IH.
      - unfold S2.veq, S3.veq. destruct x1, x2; try reflexivity. destruct (c_eq b b0); reflexivity.
  Qed.
*)

(* this is false 
  Lemma fold_v_tml_sem2 g tml Html h :
           (fun rl => fold_right2 (fun r0 V0 acc => 
              acc && negb (S2.is_bfalse (S2.veq r0 V0)))%bool true (length tml) rl (Ev.v_tml_sem g tml Html h))
           = (fun rl => fold_right2 (fun r0 V0 acc => 
              acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool true (length tml) rl (Ev.v_tml_sem g tml Html h)).
  Proof.
    extensionality rl.
    eapply (Vector.rect2 (fun n rl0 tml0 => 
      (fold_right2 (fun (r0 V0 : option BaseConst) (acc : bool) => (acc && negb (S2.is_bfalse (S2.veq r0 V0)))%bool) true n rl0 tml0 =
       fold_right2 (fun (r0 V0 : option BaseConst) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool) true n rl0 tml0)) 
      _ _ rl (Ev.v_tml_sem g tml Html h)). Unshelve.
    + reflexivity.
    + intros n v1 v2 IH x1 x2. simpl. f_equal.
      - apply IH.
      - unfold S2.veq, S3.veq. destruct x1, x2; try reflexivity. destruct (c_eq b b0); reflexivity.
        unfold S2.
  Qed.
*)

(*
  Lemma cond_sem_ex_selstar d g q s Hs Hq tml Hff Hc h :
    0 <? Rel.card (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h) (fun Vl => S2.is_btrue (SQLSem2.cond_sem d (s :: g)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in ((t IS NULL) OR cndeq t (tmvar (1, a))) AND acc) 
                          (TRUE) (combine tml s)) Hc (Ev.env_app _ _ (Ev.env_of_tuple (s :: List.nil) (cast _ _ Hs Vl)) h)))) = false ->
    S2.is_btrue (SQLSem2.cond_sem d g 
     (NOT (EXISTS (SELECT * FROM tbquery (ttquery d q) :: Datatypes.nil
      WHERE List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in ((t IS NULL) OR cndeq t (tmvar (1, a))) AND acc) 
              (TRUE) (combine tml s)))) Hff h) = true.
  Proof.
    intros Hmain.
    dependent inversion Hff with (fun G0 c0 Hinv => forall h0, h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d G0 c0 Hinv h0) = true).
    intros. rewrite H0. clear h0 H0. simpl. repeat rewrite eq_rect_r_eq_refl.
    dependent inversion j with (fun G0 c0 Hinv => forall h0, h0 ~= h -> S2.is_btrue (S2.bneg (SQLSem2.cond_sem d G0 c0 Hinv h0)) = true).
    intros. rewrite H2. clear h0 H2. simpl. repeat rewrite eq_rect_r_eq_refl.
    dependent inversion j0 with 
      (fun G0 Q0 Hinv => forall h0, h0 ~= h -> S2.is_btrue
        (S2.bneg (S2.of_bool (0 <? Rel.card (projT2
           (SQLSem2.inner_q_sem d G0 Q0 Hinv h0))))) = true).
    intros. rewrite H4. clear h0 H4. simpl.
    admit.
  Admitted.
*)

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

Lemma filter_true A p (l : list A) : 
  (forall x, List.In x l -> p x = true) -> filter p l = l.
elim l. auto.
intros h t IH Hp. simpl. rewrite Hp.
+ f_equal. apply IH. intros. apply Hp. right. exact H.
+ left. reflexivity.
Qed.

  Lemma NoDup_filter {A} (f : A -> bool) l : List.NoDup l -> List.NoDup (filter f l).
  Proof.
    elim l; simpl; auto.
    intros. inversion H0. destruct (f a); simpl; auto.
    constructor; auto. intro; apply H3.
    destruct (proj1 (filter_In f a l0) H5). exact H6.
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

  Lemma count_occ_In_Sn {A} Hdec (x : A) l: List.In x l -> exists n, count_occ Hdec l x = S n.
  Proof.
    intro Hx. assert (count_occ Hdec l x > 0).
    apply count_occ_In. exact Hx.
    inversion H; eexists; auto.
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

  Lemma card_sum_tech {m} {n} (R : Rel.R m) (f : Rel.T m -> Rel.T n) l1 : 
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
    + apply card_sum_tech.
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

  Lemma eq_memb_dep m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n) r1 r2,
    S1 ~= S2 -> r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2.
  Proof.
    rewrite e. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma p_ext_dep m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n),
      (forall r1 r2, r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2) -> S1 ~= S2.
  Proof.
    rewrite e. intros. apply eq_JMeq. apply Rel.p_ext. 
    intro. apply H. reflexivity.
  Qed.

  Lemma JMeq_eq_rect_r A T (a1 a2: A) (e : a1 = a2) (p : A -> Type) :
    forall (x : p a2) (y : T), x ~= y -> eq_rect_r p x e ~= y.
  Proof.
    rewrite e. intros. rewrite eq_rect_r_eq_refl. exact H.
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
    rewrite e. intro. rewrite (UIP _ _ ef). intros.
    unfold cast. reflexivity.
  Qed.

(*
  Lemma cond_sem_ex_selstar_aux d g q s s0 Hq tml Hs0 (Hlens: length s = length s0) Hff Hc h :
    forall h0, h0 ~= h -> (* s0 = freshlist (length tml) -> *)
    S2.is_btrue (SQLSem2.cond_sem d g 
     (EXISTS (SELECT * FROM (tbquery (ttquery d q), s0) :: Datatypes.nil
      WHERE List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc)
              (TRUE) (combine tml s0))) Hff h0) =
    (0 <? Rel.card (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h) (fun Vl => S2.is_btrue (SQLSem2.cond_sem d (s0 :: g)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s0)) Hc (Ev.env_app _ _ (Ev.env_of_tuple (s0 :: List.nil) (cast _ _ Hs0 Vl)) h))))).
(*
after changing inner_q_sem to bool

  Proof.
    dependent inversion Hff with (fun G0 c0 Hinv => forall h0, h0 ~= h -> (* s0 = freshlist (length tml) -> *)
S2.is_btrue
  (SQLSem2.cond_sem d G0 c0 Hinv h0) =
(0 <?
 Rel.card
   (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h)
      (fun Vl : Rel.T (length s) =>
       S2.is_btrue
         (SQLSem2.cond_sem d (s0 :: g)
            (List.fold_right
               (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
               (combine tml s0)) Hc
            (Ev.env_app (s0 :: Datatypes.nil) g
               (Ev.env_of_tuple (s0 :: Datatypes.nil)
                  (cast (Rel.T (length s)) (Rel.T (list_sum (List.map (length (A:=Name)) (s0 :: Datatypes.nil))))
                     Hs0 Vl)) h)))))).
    intros h0 Hh0; simpl; repeat rewrite eq_rect_r_eq_refl.
    unfold S2.is_btrue, S2.of_bool. generalize h0 Hh0; clear h0 Hh0.
    dependent inversion j with (fun G0 q1 Hinv => forall h0, h0 ~= h ->
(0 <?
 Rel.card
   (projT2
      (SQLSem2.inner_q_sem d G0 q1 Hinv h0))) =
(0 <?
 Rel.card
   (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h)
      (fun Vl : Rel.T (length s) =>
       SQLSem2.cond_sem d (s0 :: g)
         (List.fold_right
            (fun (ta : pretm * Name) (acc : precond) =>
             let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
            (combine tml s0)) Hc
         (Ev.env_app (s0 :: Datatypes.nil) g
            (Ev.env_app (s0 :: Datatypes.nil) Datatypes.nil
               (existT (fun h1 : Ev.preenv => length (s0 ++ Datatypes.nil) = length h1)
                  (to_list (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl))))
                  (eq_ind_r (fun n : nat => length (s0 ++ Datatypes.nil) = n)
                     (eq_ind_r (fun n : nat => n = length s0)
                        (Decidable.dec_not_not (length s0 + 0 = length s0)
                           (dec_eq_nat (length s0 + 0) (length s0))
                           (fun H0 : length s0 + 0 <> length s0 =>
                            eq_ind_r (fun x : Z => Zne x (Z.of_nat (length s0)) -> False)
                              (fun H2 : Zne (Z.of_nat (length s0) + 0) (Z.of_nat (length s0)) =>
                               ex_ind
                                 (fun (Zvar0 : Z)
                                    (Omega2 : Z.of_nat (length s0) = Zvar0 /\ (0 <= Zvar0 * 1 + 0)%Z) =>
                                  and_ind
                                    (fun (Omega0 : Z.of_nat (length s0) = Zvar0) (_ : (0 <= Zvar0 * 1 + 0)%Z) =>
                                     eq_ind_r (fun x : Z => Zne (x + 0 + - Z.of_nat (length s0)) 0 -> False)
                                       (eq_ind_r (fun x : Z => Zne (Zvar0 + 0 + - x) 0 -> False)
                                          (fast_Zopp_eq_mult_neg_1 Zvar0
                                             (fun x : Z => Zne (Zvar0 + 0 + x) 0 -> False)
                                             (fast_Zplus_comm (Zvar0 + 0) (Zvar0 * -1)
                                                (fun x : Z => Zne x 0 -> False)
                                                (fast_Zplus_assoc (Zvar0 * -1) Zvar0 0
                                                   (fun x : Z => Zne x 0 -> False)
                                                   (fast_Zred_factor3 Zvar0 (-1)
                                                      (fun x : Z => Zne (x + 0) 0 -> False)
                                                      (fast_Zred_factor5 Zvar0 0 (fun x : Z => Zne x 0 -> False)
                                                         (fun Omega3 : Zne 0 0 => Omega3 eq_refl)))))) Omega0)
                                       Omega0 (Zne_left (Z.of_nat (length s0) + 0) (Z.of_nat (length s0)) H2))
                                    Omega2) (intro_Z (length s0))) (Nat2Z.inj_add (length s0) 0)
                              (inj_neq (length s0 + 0) (length s0) H0))) (app_length s0 Datatypes.nil))
                     (length_to_list Rel.V (length s0)
                        (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl))))))
               (existT (fun h1 : Ev.preenv => 0 = length h1) Datatypes.nil
                  eq_refl)) h))))).
  intros h0 Hh0; simpl; rewrite card_sum.
  generalize h0 Hh0 j1; clear h0 Hh0 j1.
  dependent inversion j0 with 
      (fun G0 btb0 G1 Hinv => forall h0, h0 ~= h -> 
forall
  j1 : j_cond d (G1 ++ G0)
         (List.fold_right
            (fun (ta : pretm * Name) (acc : precond) =>
             let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
            (combine tml s0)),
(0 <?
 Rel.card
   (Rel.sel (SQLSem2.btb_sem d G0 btb0 G1 Hinv h0)
      (cast (Rel.T (list_sum (List.map (length (A:=Name)) G1)) -> bool) (Rel.T (length (concat G1)) -> bool)
         (eq_rect (length (concat G1)) (fun x : nat => (Rel.T x -> bool) = (Rel.T (length (concat G1)) -> bool))
            eq_refl (list_sum (List.map (length (A:=Name)) G1)) (length_concat_list_sum Name G1))
         (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
          S2.is_btrue
            (SQLSem2.cond_sem d (G1 ++ G0)
               (List.fold_right
                  (fun (ta : pretm * Name) (acc : precond) =>
                   let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                  (TRUE) (combine tml s0)) j1 (Ev.env_app G1 G0 (Ev.env_of_tuple G1 Vl) h0)))))) =
(0 <?
 Rel.card
   (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h)
      (fun Vl : Rel.T (length s) =>
       SQLSem2.cond_sem d (s0 :: g)
         (List.fold_right
            (fun (ta : pretm * Name) (acc : precond) =>
             let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
            (combine tml s0)) Hc
         (Ev.env_app (s0 :: Datatypes.nil) g
            (Ev.env_app (s0 :: Datatypes.nil) Datatypes.nil
               (existT (fun h1 : Ev.preenv => length s0 :: Datatypes.nil = List.map (length (A:=Value)) h1)
                  (to_list (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl)))
                   :: Datatypes.nil)
                  (eq_ind_r (fun n : nat => length s0 :: Datatypes.nil = n :: Datatypes.nil) eq_refl
                     (length_to_list Rel.V (length s0)
                        (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl))))))
               (existT (fun h1 : Ev.preenv => Datatypes.nil = List.map (length (A:=Value)) h1) Datatypes.nil
                  eq_refl)) h))))).
    intros h0 Hh0. simpl. repeat rewrite eq_rect_r_eq_refl.
    generalize h0 Hh0 j2; clear h0 Hh0 j2. generalize e; clear e.
    dependent inversion j1 with (fun G0 T0 s1' Hinv => forall (e : length s1' = length s0) h0, h0 ~= h ->
  forall (j2 : j_btb d G0 Datatypes.nil g4)
  (j3 : j_cond d (s0 :: g4 ++ G0)
         (List.fold_right
            (fun (ta : pretm * Name) (acc : precond) =>
             let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
            (combine tml s0))),
(0 <?
 Rel.card
   (Rel.sel
      (eq_rect_r (fun l : list Name => Rel.R (length l))
         (eq_rect_r (fun n : nat => Rel.R n)
            (eq_rect (length s1') (fun n0 : nat => Rel.R (n0 + length (concat g4)))
              (Rel.times (SQLSem2.tb_sem d G0 false T0 s1' Hinv h0)
               (SQLSem2.btb_sem d G0 Datatypes.nil g4 j2 h0)) (length s0) e) (app_length s0 (concat g4))) 
         (concat_cons s0 g4))
      (cast (Rel.T (length s0 + list_sum (List.map (length (A:=Name)) g4)) -> bool)
         (Rel.T (length (s0 ++ concat g4)) -> bool)
         (eq_rect (length (s0 ++ concat g4))
            (fun x : nat => (Rel.T x -> bool) = (Rel.T (length (s0 ++ concat g4)) -> bool)) eq_refl
            (length s0 + list_sum (List.map (length (A:=Name)) g4)) (length_concat_list_sum Name (s0 :: g4)))
         (fun Vl : Rel.T (length s0 + list_sum (List.map (length (A:=Name)) g4)) =>
          S2.is_btrue
            (SQLSem2.cond_sem d (s0 :: g4 ++ G0)
               (List.fold_right
                  (fun (ta : pretm * Name) (acc : precond) =>
                   let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                  (TRUE) (combine tml s0)) j3
               (Ev.env_app (s0 :: g4) G0
                  (Ev.env_app (s0 :: Datatypes.nil) g4
                     (existT
                        (fun h1 : Ev.preenv => length s0 :: Datatypes.nil = List.map (length (A:=Value)) h1)
                        (to_list (fst (Ev.split Vl)) :: Datatypes.nil)
                        (eq_ind_r (fun n : nat => length s0 :: Datatypes.nil = n :: Datatypes.nil) eq_refl
                           (length_to_list Rel.V (length s0) (fst (Ev.split Vl)))))
                     (Ev.env_of_tuple g4 (snd (Ev.split Vl)))) h0)))))) =
(0 <?
 Rel.card
   (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h)
      (fun Vl : Rel.T (length s) =>
       SQLSem2.cond_sem d (s0 :: g)
         (List.fold_right
            (fun (ta : pretm * Name) (acc : precond) =>
             let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
            (combine tml s0)) Hc
         (Ev.env_app (s0 :: Datatypes.nil) g
            (Ev.env_app (s0 :: Datatypes.nil) Datatypes.nil
               (existT (fun h1 : Ev.preenv => length s0 :: Datatypes.nil = List.map (length (A:=Value)) h1)
                  (to_list (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl)))
                   :: Datatypes.nil)
                  (eq_ind_r (fun n : nat => length s0 :: Datatypes.nil = n :: Datatypes.nil) eq_refl
                     (length_to_list Rel.V (length s0)
                        (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl))))))
               (existT (fun h1 : Ev.preenv => Datatypes.nil = List.map (length (A:=Value)) h1) Datatypes.nil
                  eq_refl)) h))))).
  intros e h0 Hh0 j3 j4. simpl. repeat rewrite eq_rect_r_eq_refl. generalize j2 j4 h0 Hh0; clear j2 j4 h0 Hh0.
  dependent inversion j3 with (fun G0 btb1 G1 Hinv => 
    forall (j2 : j_query d G0 (ttquery d q) s1)
      (j4 : j_cond d (s0 :: G1 ++ G0)
          (List.fold_right
             (fun (ta : pretm * Name) (acc : precond) =>
              let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
             (combine tml s0))) h0, h0 ~= h ->
(0 <?
 Rel.card
   (Rel.sel
      (eq_rect_r (fun l : list Name => Rel.R (length l))
         (eq_rect_r (fun n0 : nat => Rel.R n0)
            (eq_rect (length s1) (fun n0 : nat => Rel.R (n0 + length (concat G1)))
               (Rel.times (SQLSem2.q_sem d G0 (ttquery d q) s1 j2 h0) (SQLSem2.btb_sem d G0 btb1 G1 Hinv h0))
               (length s0) e) (app_length s0 (concat G1))) (concat_cons s0 G1))
      (cast (Rel.T (length s0 + list_sum (List.map (length (A:=Name)) G1)) -> bool)
         (Rel.T (length (s0 ++ concat G1)) -> bool)
         (eq_rect (length (s0 ++ concat G1))
            (fun x : nat => (Rel.T x -> bool) = (Rel.T (length (s0 ++ concat G1)) -> bool)) eq_refl
            (length s0 + list_sum (List.map (length (A:=Name)) G1)) (length_concat_list_sum Name (s0 :: G1)))
         (fun Vl : Rel.T (length s0 + list_sum (List.map (length (A:=Name)) G1)) =>
          S2.is_btrue
            (SQLSem2.cond_sem d (s0 :: G1 ++ G0)
               (List.fold_right
                  (fun (ta : pretm * Name) (acc : precond) =>
                   let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                  (TRUE) (combine tml s0)) j4
               (Ev.env_app (s0 :: G1) G0
                  (Ev.env_app (s0 :: Datatypes.nil) G1
                     (existT (fun h1 : Ev.preenv => length s0 :: Datatypes.nil = List.map (length (A:=Value)) h1)
                        (to_list (fst (Ev.split Vl)) :: Datatypes.nil)
                        (eq_ind_r (fun n0 : nat => length s0 :: Datatypes.nil = n0 :: Datatypes.nil) eq_refl
                           (length_to_list Rel.V (length s0) (fst (Ev.split Vl)))))
                     (Ev.env_of_tuple G1 (snd (Ev.split Vl)))) h0)))))) =
(0 <?
 Rel.card
   (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h)
      (fun Vl : Rel.T (length s) =>
       SQLSem2.cond_sem d (s0 :: g)
         (List.fold_right
            (fun (ta : pretm * Name) (acc : precond) =>
             let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
            (combine tml s0)) Hc
         (Ev.env_app (s0 :: Datatypes.nil) g
            (Ev.env_app (s0 :: Datatypes.nil) Datatypes.nil
               (existT (fun h1 : Ev.preenv => length s0 :: Datatypes.nil = List.map (length (A:=Value)) h1)
                  (to_list (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl)))
                   :: Datatypes.nil)
                  (eq_ind_r (fun n0 : nat => length s0 :: Datatypes.nil = n0 :: Datatypes.nil) eq_refl
                     (length_to_list Rel.V (length s0)
                        (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl))))))
               (existT (fun h1 : Ev.preenv => Datatypes.nil = List.map (length (A:=Value)) h1) Datatypes.nil eq_refl))
            h))))).
  intros j4 j5 h0 Hh0. rewrite Hh0. (* subst. *) simpl. repeat rewrite eq_rect_r_eq_refl.
  generalize (app_length s0 Datatypes.nil). intro e'.
  f_equal.
  enough (Hs1 : s1 = s).
  + apply eq_card_dep.
    - rewrite Hlens. rewrite app_nil_r. reflexivity.
    - apply eq_sel.
      * rewrite Hlens. rewrite app_nil_r. reflexivity.
      * generalize e j4 e'. clear e j4 e'. rewrite Hs1. intros. apply eq_memb_dep.
        ++ rewrite Hlens. rewrite app_nil_r. reflexivity.
        ++ apply (JMeq_eq_rect_r _ _ _ _ _ (fun l => Rel.R (length l)) _ _).
           apply JMeq_eq_rect_r. apply p_ext_dep.
           -- omega.
           -- rewrite <- e. intros. rewrite eq_rect_eq_refl.
              rewrite (Rel.p_times _ _ _ _ _ r3 (Vector.nil _)).
              ** rewrite Rel.p_one. rewrite mult_1_r.
                 f_equal. apply JMeq_eq. apply SQLSem2.q_sem_pi. reflexivity.
              ** apply JMeq_eq. eapply (JMeq_trans H16). elim r3; intuition.
        ++ exact H14.
      * generalize j5; clear j5. rewrite Hs0. intro j5. intros. simpl.
        enough (Rel.T (length (s0 ++ Datatypes.nil)) = Rel.T (length s0 + 0)).
        ++ rewrite (eq_cast_fun _ _ _ H16). f_equal.
           enough (cast (Rel.T (length (s0 ++ Datatypes.nil))) (Rel.T (length s0 + 0)) H16 r1 = r2).
                  (* cast (Rel.T (length s)) (Rel.T (length s + 0)) Hs r2).  *)
           -- rewrite H17. apply JMeq_eq. apply SQLSem2.cond_sem_pi. reflexivity.
           -- generalize r1 r2 H14; clear r1 r2 H14. rewrite H16. simpl. intros.
              rewrite H14. reflexivity.
        ++ rewrite app_nil_r. rewrite plus_0_r. reflexivity.
  + pose (jq_q_schema _ _ _ _ Hq).
    pose (jq_q_schema _ _ _ _ j4).
    rewrite e0 in e1. injection e1. intuition.
  Qed.
*)
    admit.
  Admitted.

(*
  Lemma cond_sem_ex_selstar_aux d g q s s0 Hq tml Hs0 (Hlens: length s = length s0) Hff Hc h :
    forall h0, h0 ~= h -> (* s0 = freshlist (length tml) -> *)
    S2.is_btrue (SQLSem2.cond_sem d g 
     (EXISTS (SELECT * FROM (tbquery (ttquery d q), s0) :: Datatypes.nil
      WHERE List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in ((t IS NULL) OR cndeq t (tmvar (0, a))) AND acc) 
              (TRUE) (combine tml s0))) Hff h0) =
    (0 <? Rel.card (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h) (fun Vl => S2.is_btrue (SQLSem2.cond_sem d (s0 :: g)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in ((t IS NULL) OR cndeq t (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s0)) Hc (Ev.env_app _ _ (Ev.env_of_tuple (s0 :: List.nil) (cast _ _ Hs0 Vl)) h))))).
*)
  Lemma cond_sem_ex_selstar d g q s s0 Hq tml Hs0 (Hlens : length s = length s0) Hff Hc h :
    S2.is_btrue (SQLSem2.cond_sem d g 
     (EXISTS (SELECT * FROM (tbquery (ttquery d q), s0) :: Datatypes.nil
      WHERE List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
              (TRUE) (combine tml s0))) Hff h) =
    (0 <? Rel.card (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h) (fun Vl => S2.is_btrue (SQLSem2.cond_sem d (s0 :: g)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s0)) Hc (Ev.env_app _ _ (Ev.env_of_tuple (s0 :: List.nil) (cast _ _ Hs0 Vl)) h))))).
  Proof.
    apply cond_sem_ex_selstar_aux; auto.
  Qed.

  Lemma cond_sem_not_ex_selstar d g q s s0 Hq tml Hs0 (Hlens : length s = length s0) Hff Hc h :
    S2.is_btrue (SQLSem2.cond_sem d g 
     (NOT (EXISTS (SELECT * FROM (tbquery (ttquery d q), s0) :: Datatypes.nil
      WHERE List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
              (TRUE) (combine tml s0)))) Hff h) =
    negb (0 <? Rel.card (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h) (fun Vl => S2.is_btrue (SQLSem2.cond_sem d (s0 :: g)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s0)) Hc (Ev.env_app _ _ (Ev.env_of_tuple (s0 :: List.nil) (cast _ _ Hs0 Vl)) h))))).
  Proof.
    cut (forall (h0 : Ev.env g), h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d g 
     (NOT (EXISTS (SELECT * FROM (tbquery (ttquery d q), s0) :: Datatypes.nil
      WHERE List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
                let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
              (TRUE) (combine tml s0)))) Hff h0) =
    negb (0 <? Rel.card (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h) (fun Vl => S2.is_btrue (SQLSem2.cond_sem d (s0 :: g)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s0)) Hc (Ev.env_app _ _ (Ev.env_of_tuple (s0 :: List.nil) (cast _ _ Hs0 Vl)) h)))))).
    intro Hcut. apply (Hcut h). reflexivity.
    dependent inversion Hff with (fun G0 c0 Hinv => forall h0, h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d G0 c0 Hinv h0) = 
      negb (0 <? Rel.card (Rel.sel (SQLSem2.q_sem d g (ttquery d q) s Hq h) (fun Vl =>
         S2.is_btrue (SQLSem2.cond_sem d (s0 :: g) (List.fold_right (fun (ta : pretm * Name) (acc : precond) =>
           let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s0)) Hc
              (Ev.env_app (s0 :: Datatypes.nil) g (Ev.env_of_tuple (s0 :: Datatypes.nil)
                (cast _ _ Hs0 Vl)) h)))))).
    intros. rewrite H0. clear h0 H0. simpl. repeat rewrite eq_rect_r_eq_refl.
    cut (forall b1 b2, S2.is_btrue b1 = b2 -> S2.is_btrue (S2.bneg b1) = negb b2).
    + intro Hcut. apply Hcut. rewrite -> (cond_sem_ex_selstar _ _ _ _ _ Hq _ Hs0 Hlens j Hc _). reflexivity.
    + unfold S2.is_btrue, S2.bneg. intros. rewrite H0. reflexivity.
  Qed.
*)

Lemma pred_impl_fs_sel n S p q :
  (forall (t : Rel.T n), p t = true -> q t = true) ->
  forall x, Rel.memb (Rel.sel S p) x <= Rel.memb (Rel.sel S q) x.
Proof.
  intros Hpq x. destruct (p x) eqn:ep.
  + rewrite (Rel.p_selt _ _ _ _ ep). rewrite (Rel.p_selt _ _ _ _ (Hpq _ ep)). reflexivity.
  + rewrite (Rel.p_self _ _ _ _ ep). intuition.
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

Lemma le_1_or : forall x, x <= 1 -> x = 0 \/ x = 1.
Proof.
  intros. inversion H. auto. inversion H1. auto.
Qed.

(*
Lemma impl_count_occ n Hdec (S : Rel.R n) p q ul :
  (forall vl, p vl = true -> q vl = true) ->
  count_occ Hdec (Rel.supp (Rel.sel S p)) ul <= count_occ Hdec (Rel.supp (Rel.sel S q)) ul.
Proof.
  intro.
*)

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

(*
Lemma v_tml_sem_cons g t tml H Ht Html h :
  Ev.v_tml_sem g (t :: tml) H h = cons _ (Ev.tm_sem g t Ht h) _ (Ev.v_tml_sem g tml Html h).
Proof.
  unfold Ev.v_tml_sem at 1. apply JMeq_eq. rewrite <- (Ev.p_tml_sem g (t::tml) H h).
  rewrite eq_rect_eq_refl. simpl. apply Vector_cons_equal.
  + rewrite Ev.p_tml_sem. reflexivity.
  + apply Ev.tm_sem_pi. reflexivity.
  + unfold Ev.v_tml_sem. rewrite <- Ev.p_tml_sem. rewrite eq_rect_eq_refl.
    apply of_list_equal. apply JMeq_eq. apply Ev.tml_sem_pi. reflexivity.
Qed.
*)

  Lemma S2_is_btrue_or_elim (b1 b2 : bool) (P : Prop) :
    (S2.is_btrue b1 = true -> P) -> (S2.is_btrue b2 = true -> P) ->
    S2.is_btrue (b1 || b2) = true -> P.
  Proof.
    Bool.destr_bool; auto.
  Qed.

  Definition projT1_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : projT1 u = projT1 v
    := f_equal (@projT1 _ _) p.

  Definition projT2_eq {A} {P : A -> Type} {u v : { a : A & P a }} (p : u = v)
    : @eq_rect _ _ _ (projT2 u) _ (projT1_eq p) = projT2 v.
  Proof.
    rewrite p. reflexivity.
  Qed.

  Lemma f_JMeq : forall A (T : A -> Type) (f : forall a, T a) x y, x = y -> f x ~= f y.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.

  Definition existT_projT2_eq {A} {P : A -> Type} a (p1 p2 :  P a) (e : existT _ _ p1 = existT _ _ p2)
    : p1 = p2.
  Proof.
    transitivity (projT2 (existT P a p1)). reflexivity. 
    transitivity (projT2 (existT P a p2)). apply JMeq_eq. eapply (f_JMeq _ _ (@projT2 A P) _ _ e).
    reflexivity.
  Qed.

(*

Lemma cond_sem_cndeq_false1 d G t1 t2 Ht1 Hc h :
  Ev.tm_sem G t1 Ht1 h = None ->
  SQLSem2.cond_sem d G (cndeq t1 t2) Hc h = false.
Proof.
  intro Hsem1. cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d _ _ Hc h0 = false).
  + intro Hcut; apply Hcut; reflexivity.
  + dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h -> SQLSem2.cond_sem d G0 c0 Hinv h0 = false).
    generalize p0 H2; clear p0 H2; rewrite <- e. intros p0 H2.
    simpl in p0. pose (existT_projT2_eq _ _ _ H2). clearbody e0.
    simpl. intros h0 Hh0; rewrite Hh0; clear h0 Hh0. repeat rewrite eq_rect_r_eq_refl.
    transitivity (S2.sem_bpred 2 p0 ((fun HWF => 
      Ev.tm_sem G t1 (HWF t1 (or_introl eq_refl)) h
      ::(fun HWF0 => Ev.tm_sem G t2 (HWF0 t2 (or_introl eq_refl)) h
      :: Datatypes.nil) (fun t H0 => HWF t (or_intror H0))) j0) (Ev.p_tml_sem G (t1::t2::Datatypes.nil) j0 h)).
    reflexivity. rewrite e0. clear H2.
    apply S2.sem_bpred_elim.
    - intro. replace (Ev.tm_sem G t1 (j0 t1 (or_introl eq_refl)) h) with (Ev.tm_sem G t1 Ht1 h).
      * rewrite Hsem1. simpl. 
        destruct (bind (Ev.tm_sem G t2 (j0 t2 (or_intror (or_introl eq_refl))) h)
          (fun b : BaseConst => ret (b :: Datatypes.nil))); simpl; intro Hfalse; discriminate Hfalse.
      * apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
    - auto.
Qed.

Lemma cond_sem_cndeq_false2 d G t1 t2 Ht2 Hc h :
  Ev.tm_sem G t2 Ht2 h = None ->
  SQLSem2.cond_sem d G (cndeq t1 t2) Hc h = false.
Proof.
  intro Hsem1. cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d _ _ Hc h0 = false).
  + intro Hcut; apply Hcut; reflexivity.
  + dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h -> SQLSem2.cond_sem d G0 c0 Hinv h0 = false).
    generalize p0 H2; clear p0 H2; rewrite <- e. intros p0 H2.
    simpl in p0. pose (existT_projT2_eq _ _ _ H2). clearbody e0.
    simpl. intros h0 Hh0; rewrite Hh0; clear h0 Hh0. repeat rewrite eq_rect_r_eq_refl.
    transitivity (S2.sem_bpred 2 p0 ((fun HWF => 
      Ev.tm_sem G t1 (HWF t1 (or_introl eq_refl)) h
      ::(fun HWF0 => Ev.tm_sem G t2 (HWF0 t2 (or_introl eq_refl)) h
      :: Datatypes.nil) (fun t H0 => HWF t (or_intror H0))) j0) (Ev.p_tml_sem G (t1::t2::Datatypes.nil) j0 h)).
    reflexivity. rewrite e0. clear H2.
    apply S2.sem_bpred_elim.
    - intro. destruct (Ev.tm_sem G t1 (j0 t1 (or_introl eq_refl)) h); simpl.
      * replace (Ev.tm_sem G t2 (j0 t2 (or_intror (or_introl eq_refl))) h) with (Ev.tm_sem G t2 Ht2 h).
        ++ rewrite Hsem1. simpl. intro Hfalse. discriminate Hfalse.
        ++ apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
      * replace (Ev.tm_sem G t2 (j0 t2 (or_intror (or_introl eq_refl))) h) with (Ev.tm_sem G t2 Ht2 h).
        ++ rewrite Hsem1. simpl. intro Hfalse. discriminate Hfalse.
        ++ apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
    - auto.
Qed.


Lemma cond_sem_cndeq_true1 d G t1 t2 Ht1 Ht2 Hc h k :
  Ev.tm_sem G t1 Ht1 h = Some k -> Ev.tm_sem G t2 Ht2 h = Some k ->
  SQLSem2.cond_sem d G (cndeq t1 t2) Hc h = true.
Proof.
  intros Hsem1 Hsem2. cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d _ _ Hc h0 = true).
  + intro Hcut; apply Hcut; reflexivity.
  + dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h -> 
      SQLSem2.cond_sem d G0 c0 Hinv h0 = true).
    generalize p0 H2; clear p0 H2; rewrite <- e. intros p0 H2.
    simpl in p0. pose (existT_projT2_eq _ _ _ H2). clearbody e0.
    simpl. intros h0 Hh0; rewrite Hh0; clear h0 Hh0. repeat rewrite eq_rect_r_eq_refl.
    cut (S2.sem_bpred 2 p0 ((fun HWF => 
      Ev.tm_sem G t1 (HWF t1 (or_introl eq_refl)) h
      ::(fun HWF0 => Ev.tm_sem G t2 (HWF0 t2 (or_introl eq_refl)) h
      :: Datatypes.nil) (fun t H0 => 
      HWF t (or_intror H0))) j0) (Ev.p_tml_sem G (t1::t2::Datatypes.nil) j0 h) = true). intro Hcut. apply Hcut.
    apply S2.sem_bpred_elim.
    - intro. replace (Ev.tm_sem G t1 (j0 t1 (or_introl eq_refl)) h) with (Ev.tm_sem G t1 Ht1 h).
      * replace (Ev.tm_sem G t2 (j0 t2 (or_intror (or_introl eq_refl))) h) with (Ev.tm_sem G t2 Ht2 h).
        ++ rewrite Hsem1, Hsem2. simpl.
           unfold ret. intro Hinj. injection Hinj. intro Hcl.
           rewrite <- Hcl. simpl. intro Htriv. rewrite e0.
           rewrite (UIP _ _ Htriv). simpl. repeat rewrite eq_rect_r_eq_refl. 
           unfold S2.of_bool, nth_lt. simpl. apply Db.BaseConst_eqb_eq. reflexivity.
        ++ apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
      * apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
    - replace (Ev.tm_sem G t1 (j0 t1 (or_introl eq_refl)) h) with (Ev.tm_sem G t1 Ht1 h).
      * replace (Ev.tm_sem G t2 (j0 t2 (or_intror (or_introl eq_refl))) h) with (Ev.tm_sem G t2 Ht2 h).
        ++ rewrite Hsem1, Hsem2. simpl. unfold ret. intro Hfalse. discriminate Hfalse.
        ++ apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
      * apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
Qed.

Lemma cond_sem_cndeq_true2 d G t1 t2 Ht1 Ht2 Hc h :
  SQLSem2.cond_sem d G (cndeq t1 t2) Hc h = true -> 
  exists k, Ev.tm_sem G t1 Ht1 h = Some k /\ Ev.tm_sem G t2 Ht2 h = Some k.
Proof.
  cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d _ _ Hc h0 = true -> 
    exists k, Ev.tm_sem G t1 Ht1 h = Some k /\ Ev.tm_sem G t2 Ht2 h = Some k).
  + intro Hcut; apply Hcut; reflexivity.
  + dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h -> 
      SQLSem2.cond_sem d G0 c0 Hinv h0 = true -> 
      exists k : BaseConst, Ev.tm_sem G t1 Ht1 h = Some k /\ Ev.tm_sem G t2 Ht2 h = Some k).
    generalize p0 H2; clear p0 H2; rewrite <- e. intros p0 H2.
    simpl in p0. pose (existT_projT2_eq _ _ _ H2). clearbody e0.
    simpl. intros h0 Hh0; rewrite Hh0; clear h0 Hh0. repeat rewrite eq_rect_r_eq_refl.
    cut (S2.sem_bpred 2 p0 ((fun HWF => 
      Ev.tm_sem G t1 (HWF t1 (or_introl eq_refl)) h
      ::(fun HWF0 => Ev.tm_sem G t2 (HWF0 t2 (or_introl eq_refl)) h
      :: Datatypes.nil) (fun t H0 => HWF t (or_intror H0))) j0) (Ev.p_tml_sem G (t1::t2::Datatypes.nil) j0 h) = true
      -> exists k : BaseConst, Ev.tm_sem G t1 Ht1 h = Some k /\ Ev.tm_sem G t2 Ht2 h = Some k). intro Hcut. apply Hcut.
    apply S2.sem_bpred_elim.
    - intro. destruct (Ev.tm_sem G t2 (j0 t2 (or_intror (or_introl eq_refl))) h) eqn:Hk2; simpl.
      * destruct (Ev.tm_sem G t1 (j0 t1 (or_introl eq_refl)) h) eqn:Hk1; simpl.
        ++ unfold ret. intro Hinj; injection Hinj; clear Hinj. intro Hcl. rewrite <- Hcl.
          simpl. intro Htriv. rewrite e0.
          rewrite (UIP _ _ Htriv). simpl. repeat rewrite eq_rect_r_eq_refl. 
          unfold S2.of_bool, nth_lt. simpl. intro Heq. cut (b0 = b).
          -- intro Hcut. exists b. split.
            ** rewrite <- Hcut. rewrite <- Hk1. apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
            ** rewrite <- Hk2. apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
          -- apply Db.BaseConst_eqb_eq. exact Heq.
        ++ intro Hfalse; discriminate Hfalse.
      * intro Hfalse; discriminate Hfalse.
    - intros _ Hfalse. discriminate Hfalse.
Qed.
*)

Lemma list_In_vec_In {A} (a : A) (l : list A) : List.In a l -> Vector.In a (Vector.of_list l).
Proof.
  elim l.
  + intro H. contradiction H.
  + intros a0 l0 IH H. destruct H.
    - rewrite H. constructor.
    - constructor. apply IH. exact H.
Qed.

(*
Definition j_var_findpos a s :
  j_var a s -> 
  forall m, { n : nat & n < m + length s /\ findpos s (fun x => if Db.Name_dec x a then true else false) m = Some n }.
intro H. elim H; simpl.
  + intros. exists m. destruct (Db.Name_dec a a); intuition.
  + intros. destruct (Db.Name_dec b a); intuition.
    - rewrite e in n. contradiction n. reflexivity.
    - destruct (H0 (S m)). destruct a0.
      exists x. split; auto; omega.
Defined.
*)
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

(*
Definition is_subenv {n} (ul : Rel.T n) {m} {s} {g} (Hlen : length s = m + n) (h : Ev.env (s::g)) := 
  forall a (Ha: j_var a s) k (Hk : k < n), proj1_sig (Fin.to_nat (Fin_findpos a s Ha)) = k + m ->
  Ev.var_sem 0 _ (s::g) _ eq_refl Ha h = nth ul (Fin.of_nat_lt Hk).

Lemma cons_is_subenv t {n} (ul : Rel.T n) {s} {g} (h : Ev.env (s::g)) :
  forall m m' (H1 : length s = m + S n) (H2 : length s = m' + n), 
  is_subenv (cons _ t _ ul) H1 h -> is_subenv ul H2 h.
Proof.
  intros. unfold is_subenv. intros. cut (S k < S n).
  + intro HSk. replace (nth ul (Fin.of_nat_lt Hk)) with (nth (cons _ t _ ul) (Fin.of_nat_lt HSk)).
    - apply H. rewrite H0. omega.
    - simpl. f_equal. apply Fin.of_nat_ext.
  + omega.
Qed.

Lemma eq_is_subenv {m} (ul : Rel.T m) {n} (vl : Rel.T n) {s} {g} (h : Ev.env (s::g)) : 
  m = n ->
  forall k (Hul : length s = k + m) (Hvl : length s = k + n), ul ~= vl -> is_subenv ul Hul h -> is_subenv vl Hvl h.
Proof.
  intro. generalize ul; clear ul; rewrite H; intro ul.
  intros k Hul Hvl e. generalize Hul; clear Hul; rewrite e; intro Hul. intro Hsub.
  unfold is_subenv. intros. apply Hsub. exact H0.
Qed.
*)

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

Lemma bool_eq_P (P : Prop) b1 b2 : (b1 = true <-> P) -> (b2 = true <-> P) -> b1 = b2.
Proof.
  Bool.destr_bool.
  + apply H. apply H0. reflexivity.
  + symmetry. apply H0. apply H. reflexivity.
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

Lemma cond_sem_cndeq_true1' d G t1 t2 St1 St2 h k :
  Ev.j_tm_sem G t1 St1 -> Ev.j_tm_sem G t2 St2 ->
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
      rewrite (UIP _ _ Htriv). rewrite H. repeat rewrite eq_rect_r_eq_refl. 
      unfold S2.of_bool, nth_lt. simpl. apply Db.BaseConst_eqb_eq. reflexivity.
    - simpl. rewrite eSt1, eSt2. simpl. intro Hfalse. discriminate Hfalse. 
      Unshelve. reflexivity.
Qed.

(*
Lemma cond_sem_not_neq_iff d g s tml (Hlen : length s = length tml) : 
  forall Html Hc (ul : Rel.T (length tml)), 
  forall h h' h'', h = Ev.env_app (s::List.nil) _ h'' h' -> is_subenv ul (Hlen : length s = 0 + length tml) h ->
  SQLSem2.cond_sem d (s :: g)%list 
    (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s)) 
    Hc h = true
  <-> forall i, S3.is_bfalse (S3.veq (nth ul i) (nth (Ev.v_tml_sem g tml Html h') i)) = false.
Proof.
  eapply (@list_rect2 _ _ (fun s0 tml0 =>
    forall s1, s = s1 ++ s0 ->
    forall (Hlen0: length s = length s1 + length tml0),
    forall Html Hc (ul: Rel.T (length tml0)) h h' h'', 
    h = Ev.env_app (s::List.nil) _ h'' h' -> 
    is_subenv ul Hlen0 h ->
    SQLSem2.cond_sem d (s :: g)
      (List.fold_right (fun (ta : pretm * Name) acc =>
        let (t,a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml0 s0)) Hc h = true
    <-> (forall i, S3.is_bfalse (S3.veq (nth ul i) (nth (Ev.v_tml_sem g tml0 Html h') i)) = false))
    _ _ _ _  Hlen List.nil eq_refl Hlen). Unshelve.
  + simpl. intros. split; intro.
    - intro. inversion i.
    - generalize h. 
      dependent inversion Hc with (fun G0 c0 Hinv =>
          forall (h0 : Ev.env G0), SQLSem2.cond_sem d G0 c0 Hinv h0 = true).
      intros. reflexivity.
  + simpl. intros x t s0 tml0 Hlen0 IH s1 Hs Hlens Html0 Hc ul h h' h'' Happ Hsub. split; intro.
    - intro i. cut (forall Ht, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = Db.null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
      * generalize Hsub; clear Hsub.
        cut (forall i0 (ul1 : Rel.T (S (length tml0))), i0 ~= i -> ul1 ~= ul -> 
          is_subenv ul1 Hlens h ->
          (forall Ht : j_tm g t, nth ul1 Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul1 Fin.F1) ->
          S3.is_bfalse (S3.veq (nth ul i0) (nth (Ev.v_tml_sem g (t :: tml0) Html0 h') i)) = false). intro Hcut. apply Hcut. reflexivity. reflexivity.
        dependent inversion ul with (fun m (ul0 : Rel.T m) => forall i0 (ul1 : Rel.T (S (length tml0))),
          i0 ~= i -> ul1 ~= ul0 -> is_subenv ul1 Hlens h ->
          (forall Ht : j_tm g t, nth ul1 Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul1 Fin.F1) ->
          S3.is_bfalse (S3.veq (nth ul0 i0) (nth (Ev.v_tml_sem g (t :: tml0) Html0 h') i)) = false).
        intros i0 ul1 Hi0 Hul1; rewrite Hi0, Hul1; clear Hi0. intro Hsub. cut ((j_tm g t * j_tml g tml0)%type).
        ++ intro. destruct X. rewrite (v_tml_sem_cons _ _ _ _ j j0 h'). intro Hcut. simpl in Hcut.
          cut (forall (ul0 vl0 : Rel.T (S (length tml0))), 
            ul0 ~= cons _ h0 _ t0 ->
            vl0 ~= cons _ (Ev.tm_sem g t j h') _ (Ev.v_tml_sem g tml0 j0 h') ->
            S3.is_bfalse (S3.veq (nth ul0 i) (nth vl0 i)) = false).
          -- intro Hcut1. apply Hcut1; reflexivity.
          -- dependent inversion i with (fun (n1 : nat) (i0 : Fin.t n1) => 
              forall ul0 vl0, ul0 ~= cons _ h0 (length tml0) t0 -> 
              vl0 ~= cons _ (Ev.tm_sem g t j h') _ (Ev.v_tml_sem g tml0 j0 h') ->
              S3.is_bfalse (S3.veq (nth ul0 i0) (nth vl0 i0)) = false);
              intros ul0 vl0 Hul0 Hvl0; rewrite Hul0, Hvl0; clear Hul0 Hvl0.
            ** simpl. destruct (Hcut j).
              +++ rewrite H0; simpl; reflexivity.
              +++ destruct H0.
                --- rewrite H0. unfold S3.veq. destruct h0; simpl; reflexivity.
                --- rewrite H0. destruct h0; simpl; try reflexivity.
                    replace (c_eq b b) with true; auto.
                    symmetry. apply Db.BaseConst_eqb_eq. reflexivity.
            ** simpl. generalize H. 
              cut (forall h0, h0 ~= h ->
                SQLSem2.cond_sem d (s :: g) (((tmvar (0, x) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))))
                   AND List.fold_right (fun (ta : pretm * Name) (acc : precond) => let (t2, a) := ta in
                   ((tmvar (0, a) IS NULL) OR ((tm_lift t2 1 IS NULL) OR cndeq (tm_lift t2 1) (tmvar (0, a)))) AND acc)
                (TRUE) (combine tml0 s0)) Hc h0 = true -> S3.is_bfalse (S3.veq (nth t0 t1) (nth (Ev.v_tml_sem g tml0 j0 h') t1)) = false).
                intro Hcut1. apply Hcut1. reflexivity.
              dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h ->
                SQLSem2.cond_sem d G0 c0 Hinv h0 = true -> S3.is_bfalse (S3.veq (nth t0 t1) (nth (Ev.v_tml_sem g tml0 j0 h') t1)) = false).
              intros h1 Hh1; rewrite Hh1; clear h1 Hh1. intro Hc'. simpl in Hc'. repeat rewrite eq_rect_r_eq_refl in Hc'.
              eapply (S2_is_btrue_and_elim _ _ _ _ Hc'). Unshelve. intros Hc1 Hc2.
              cut (length s = length (s1 ++ x :: Datatypes.nil) + length tml0).
              +++ intro Hcut1. eapply (IH _ _ Hcut1 _ j2 _ h h' h'' Happ). Unshelve.
                --- generalize Hsub. apply cons_is_subenv.
                --- apply Hc2.
                --- rewrite Hs. rewrite <- app_assoc. reflexivity.
              +++ rewrite Hs. do 2 rewrite app_length. simpl. rewrite Hlen0. omega.
        ++ split.
          -- apply Html0; left; reflexivity.
          -- intro t1. intro Ht1. apply Html0; right; apply Ht1.
      * generalize H. cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d (s :: g)
          (((tmvar (0, x) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))))
            AND List.fold_right (fun (ta : pretm * Name) (acc : precond) => let (t0, a) := ta in
            ((tmvar (0, a) IS NULL) OR ((tm_lift t0 1 IS NULL) OR cndeq (tm_lift t0 1) (tmvar (0, a)))) AND acc)
           (TRUE) (combine tml0 s0)) Hc h0 = true ->
          forall Ht : j_tm g t, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
          intro Hcut1; apply Hcut1; reflexivity.
        dependent inversion Hc with (fun G0 c0 Hinv => forall h0, h0 ~= h ->
        SQLSem2.cond_sem d G0 c0 Hinv h0 = true -> forall Ht : j_tm g t, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
        intros h1 Hh1; rewrite Hh1; clear h1 Hh1. intro Hc'. simpl in Hc'. repeat rewrite eq_rect_r_eq_refl in Hc'.
        eapply (S2_is_btrue_and_elim _ _ _ _ Hc'). Unshelve. intros Hc1 _.
        generalize Hc1; clear Hc1.
        cut (forall h0, h0 ~= h -> S2.is_btrue
              (SQLSem2.cond_sem d (s :: g) ((tmvar (0, x) IS NULL) OR 
                ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x)))) j h0) = true ->
              forall Ht : j_tm g t, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
          intro Hcut1; apply Hcut1; reflexivity.
        dependent inversion j with (fun G0 c0 Hinv => forall h0, h0 ~= h -> 
          SQLSem2.cond_sem d G0 c0 Hinv h0 = true -> forall Ht, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
        intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl. repeat rewrite eq_rect_r_eq_refl.
        intro Hc1. eapply (S2_is_btrue_or_elim _ _ _ _ _ Hc1). Unshelve.
        ++ clear Hc1.
          cut (forall h0, h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d (s :: g) (tmvar (0, x) IS NULL) j1 h0) = true ->
            forall Ht : j_tm g t, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
            intro Hcut1; apply Hcut1; reflexivity.
          dependent inversion j1 with (fun G0 c0 Hinv => forall h0, h0 ~= h -> 
            SQLSem2.cond_sem d G0 c0 Hinv h0 = true ->
            forall Ht, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
          intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl; repeat rewrite eq_rect_r_eq_refl.
          destruct (Ev.tm_sem (s::g) (tmvar (0,x)) j4 h) eqn:Hsem; unfold S2.of_bool; simpl; intuition.
        ++ cut (forall h0, h0 ~= h -> 
             S2.is_btrue (SQLSem2.cond_sem d (s :: g) ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))) j2 h0) 
                = true ->
             forall Ht : j_tm g t, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
            intro Hcut1; apply Hcut1; reflexivity.
          dependent inversion j2 with (fun G0 c0 Hinv => forall h0, h0 ~= h -> 
            SQLSem2.cond_sem d G0 c0 Hinv h0 = true -> forall Ht, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
          intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl. repeat rewrite eq_rect_r_eq_refl.
          intro Hc2. eapply (S2_is_btrue_or_elim _ _ _ _ _ Hc2). Unshelve.
          -- clear Hc2.
            cut (forall h0, h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d (s :: g) (tm_lift t 1 IS NULL) j3 h0) = true ->
              forall Ht : j_tm g t, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
              intro Hcut1; apply Hcut1; reflexivity.
            dependent inversion j3 with (fun G0 c0 Hinv => forall h0, h0 ~= h -> 
               SQLSem2.cond_sem d G0 c0 Hinv h0 = true ->
               forall Ht, nth ul Fin.F1 = null \/ Ev.tm_sem g t Ht h' = null \/ Ev.tm_sem g t Ht h' = nth ul Fin.F1).
            intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl; repeat rewrite eq_rect_r_eq_refl.
            destruct (Ev.tm_sem (s::g) (tm_lift t 1) j6 h) eqn:Hsem; unfold S2.of_bool; simpl; intuition.
          -- intro Heq. cut ((j_tm (s::g) (tm_lift t 1) * j_tm (s::g) (tmvar (0,x)))%type).
            ** intro p. destruct p. destruct (cond_sem_cndeq_true2 _ _ _ _ j5 j6 _ _ Heq).
              destruct H7. intro Ht. right. right. cut (j_var x s).
              +++ intro Hx. cut (proj1_sig (Fin.to_nat (Fin_findpos x s Hx)) = 0 + length s1).
                --- intro Hcut1. refine (let Hsub' := Hsub _ Hx 0 (lt_O_Sn _) Hcut1 in _).
                  clearbody Hsub'. transitivity (Ev.var_sem 0 x (s::g) s eq_refl Hx h).
                  *** transitivity (Some x0).
                    ++++ rewrite <- H7. rewrite Happ. apply (Ev.tm_sem_weak _ _ _ _ (s::List.nil)).
                    ++++ rewrite <- H10. dependent inversion j6 with (fun t0 Hinv =>
                          Ev.tm_sem (s::g) t0 Hinv h = Ev.var_sem 0 x (s::g) s eq_refl Hx h).
                        simpl. simpl in e. injection e. intro e'.
                        generalize e j7; clear e j7.
                        eapply (@eq_rect _ _ (fun s0 => forall (e : Some s = Some s0) (j7 : j_var x s0), 
                          Ev.var_sem 0 x (s :: g) s0 e j7 h = Ev.var_sem 0 x (s::g) s eq_refl Hx h) _ _ e').
                        Unshelve. simpl. intros. apply JMeq_eq. apply Ev.var_sem_pi. reflexivity.
                  *** rewrite Hsub'. reflexivity.
                --- generalize Hx. rewrite Hs. intro Hx0. eapply Fin_findpos_tech. reflexivity.
              +++ inversion j6. simpl in H12. injection H12. intro. rewrite H14. exact X.
            ** inversion j4. split; apply X.
              +++ left. reflexivity.
              +++ right. left. reflexivity.
    - cut (forall h1, h1 ~= h -> SQLSem2.cond_sem d (s :: g)
        (((tmvar (0, x) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))))
         AND List.fold_right (fun (ta : pretm * Name) (acc : precond) => let (t0, a) := ta in
          ((tmvar (0, a) IS NULL) OR ((tm_lift t0 1 IS NULL) OR cndeq (tm_lift t0 1) (tmvar (0, a)))) AND acc)
         (TRUE) (combine tml0 s0)) Hc h1 = true). intro Hcut1; apply Hcut1; reflexivity.
      dependent inversion Hc with (fun G0 c0 Hinv => forall h1, h1 ~= h -> SQLSem2.cond_sem d G0 c0 Hinv h1 = true).
      intros h1 Hh1; rewrite Hh1; clear h1 Hh1. simpl. repeat rewrite eq_rect_r_eq_refl.
      apply S2_is_btrue_and_intro.
      * cut (forall h0, h0 ~= h -> S2.is_btrue (SQLSem2.cond_sem d (s :: g)
           ((tmvar (0, x) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x)))) j h0) = true).
          intro Hcut1; apply Hcut1; reflexivity.
        dependent inversion j with (fun G0 c0 Hinv => forall h0, h0 ~= h -> 
          SQLSem2.cond_sem d G0 c0 Hinv h0 = true).
        intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl. repeat rewrite eq_rect_r_eq_refl.
        destruct (SQLSem2.cond_sem d (s :: g) ((tmvar (0,x)) IS NULL) j1 h) eqn:Hnull; auto.
        generalize Hnull. clear Hnull.
        cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d (s :: g) (tmvar (0, x) IS NULL) j1 h0 = false ->
          S2.bor false (SQLSem2.cond_sem d (s :: g) 
            ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))) j2 h) = true).
          intro Hcut1; apply Hcut1; reflexivity.
        dependent inversion j1 with (fun G0 c0 Hinv => forall h0, h0 ~= h ->
          SQLSem2.cond_sem d G0 c0 Hinv h0 = false -> SQLSem2.cond_sem d (s::g) ((tm_lift t 1 IS NULL) OR (cndeq (tm_lift t 1) (tmvar (0,x)))) j2 h = true).
        intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl. repeat rewrite eq_rect_r_eq_refl.
        destruct (Ev.tm_sem (s :: g) (tmvar (0, x)) j4 h) eqn:Hnull.
        ++ intros _. cut (forall h0, h0 ~= h -> SQLSem2.cond_sem d (s :: g) ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))) j2 h0 = true).
            intro Hcut1; apply Hcut1; reflexivity.
          dependent inversion j2 with (fun G0 c0 Hinv => forall h0, h0 ~= h ->
            SQLSem2.cond_sem d G0 c0 Hinv h0 = true).
          intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl; repeat rewrite eq_rect_r_eq_refl.
          cut (forall h0, h0 ~= h -> S2.bor (SQLSem2.cond_sem d (s :: g) (tm_lift t 1 IS NULL) j5 h0)
            (SQLSem2.cond_sem d (s :: g) (cndeq (tm_lift t 1) (tmvar (0, x))) j6 h) = true).
            intro Hcut1; apply Hcut1; reflexivity.
          dependent inversion j5 with (fun G0 c0 Hinv => forall h0, h0 ~= h ->
            S2.bor (SQLSem2.cond_sem d G0 c0 Hinv h0) (SQLSem2.cond_sem d (s::g) (cndeq (tm_lift t 1) (tmvar (0,x))) j6 h) = true).
          intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl; repeat rewrite eq_rect_r_eq_refl.
          cut (Ev.tm_sem (s::g) (tm_lift t 1) j8 h = null \/ Ev.tm_sem (s::g) (tm_lift t 1) j8 h = Ev.tm_sem (s::g) (tmvar (0,x)) j4 h).
          -- intro Hcut; destruct Hcut.
            ** rewrite H13; simpl. reflexivity.
            ** rewrite H13, Hnull. simpl. eapply cond_sem_cndeq_true1.
              +++ rewrite Hnull in H13. exact H13.
              +++ exact Hnull.
          -- assert (Ht : j_tm g t). apply Html0. left. reflexivity.
            replace (Ev.tm_sem (s::g) (tm_lift t 1) j8 h) with (Ev.tm_sem g t Ht h').
            ** assert (Hsuba : j_var x s).
              inversion j4. simpl in H16. injection H16. intuition.
              assert (Hsubk : 0 < S (length tml0)). omega.
              assert (Hfind : proj1_sig (Fin.to_nat (Fin_findpos x s Hsuba)) = 0 + length s1).
                rewrite (Fin_findpos_tech _ _ _ _ _ Hs). reflexivity.
              pose (Hsub' := Hsub _ Hsuba _ Hsubk Hfind). clearbody Hsub'.
              pose (H' := H Fin.F1). clearbody H'.
              replace (nth ul Fin.F1) with (nth ul (Fin.of_nat_lt Hsubk)) in H'.
              assert (Hx : Ev.tm_sem (s :: g) (tmvar (0, x)) j4 h = Ev.var_sem 0 x (s::g) s eq_refl Hsuba h).
              cut (forall h0, h0 ~= h -> Ev.tm_sem (s :: g) (tmvar (0, x)) j4 h0 = 
                Ev.var_sem 0 x (s :: g) s eq_refl Hsuba h). intro Hcut1; apply Hcut1; reflexivity.
              dependent inversion j4 with (fun t0 Hinv => forall h0, h0 ~= h ->
                  Ev.tm_sem (s::g) t0 Hinv h0 = Ev.var_sem 0 x (s::g) s eq_refl Hsuba h). simpl.
              intros h0 Hh0; rewrite Hh0; clear h0 Hh0. simpl in e. injection e. intro e'.
              generalize e j9 ; clear e j9 ; rewrite <- e'. intros.
              apply JMeq_eq. apply Ev.var_sem_pi. reflexivity.
              destruct (not_veq_false _ _ H').
              +++ rewrite <- Hsub' in H13. rewrite <- Hx in H13. rewrite Hnull in H13. discriminate H13.
              +++ erewrite v_tml_sem_cons in H13. Unshelve. Focus 2. exact Ht.
                Focus 2. intro t2. intro Ht2. apply Html0. right. exact Ht2.
                simpl in H13. destruct H13.
                --- left. exact H13.
                --- right. rewrite Hx, Hsub'. rewrite <- H13. reflexivity.
              +++ reflexivity.
            ** rewrite Happ. apply (Ev.tm_sem_weak _ _ _ _ (s::List.nil)).
        ++ unfold S2.of_bool; intro Hfalse; discriminate Hfalse.
      * generalize H; clear H. generalize (@eq_refl _ ul).
        eapply (Vector.caseS' ul (fun ul0 => ul = ul0 -> (forall i : Fin.t (S (length tml0)),
          S3.is_bfalse (S3.veq (nth ul i) (nth (Ev.v_tml_sem g (t :: tml0) Html0 h') i)) = false) ->
          S2.is_btrue (SQLSem2.cond_sem d (s :: g) (List.fold_right
            (fun (ta : pretm * Name) (acc : precond) => let (t1, a) := ta in 
              (tmvar (0,a) IS NULL) OR (((tm_lift t1 1) IS NULL) OR cndeq (tm_lift t1 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml0 s0)) j0 h) = true)).
        intros u0 ul0 Hul. rewrite Hul. intro H. cut (length s = length (s1 ++ x :: Datatypes.nil) + length tml0).
        ++ intro Hcut. eapply (IH _ _ Hcut _ _ ul0 _ h' _ Happ _). Unshelve.
          -- intro i. pose (H (Fin.FS i)). simpl in e. erewrite v_tml_sem_cons in e. apply e. Unshelve.
             apply Html0. left. reflexivity.
          -- rewrite Hs. rewrite <- app_assoc. reflexivity.
          -- intro t0. intro Ht0. apply Html0. right. exact Ht0.
          -- generalize Hsub. rewrite Hul. apply cons_is_subenv.
        ++ rewrite Hs. do 2 rewrite app_length. simpl. rewrite Hlen0. omega.
Qed.
*)

(*
Lemma cond_sem_not_neq_iff d g s tml Hc : forall ul vl,
  forall h,
  SQLSem2.cond_sem d (s :: g)%list 
    (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in ((t IS NULL) OR cndeq t (tmvar (1, a))) AND acc) (TRUE) (combine tml s)) 
    Hc (Ev.env_app _ _ (Ev.env_of_tuple (s :: List.nil) ul) h) = true
  <-> forall i, S3.is_bfalse (S3.veq (nth ul i) (nth vl i)) = false.
Proof.
  elim Hc.
*)

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


Lemma split_n_0 {A} {n} : forall (ul1 : Vector.t A (n+0)) (ul2 : Vector.t A n), ul1 ~= ul2 -> Ev.split ul1 ~= (ul2, nil A).
Proof.
  elim n.
  + simpl. intros. 
    eapply (Vector.case0 (fun ul0 => (nil A, ul0) ~= (ul2, nil A))).
    eapply (Vector.case0 (fun ul0 => (nil A, nil A) ~= (ul0, nil A))). reflexivity.
  + clear n. intros n IH ul1 ul2. simpl. intro.
    generalize (@JMeq_refl _ ul1).
    eapply (Vector.caseS (fun n0 ul0 => ul1 ~= ul0 -> (let (v1,v2) := Ev.split (tl ul1) in (cons A (hd ul1) n v1, v2)) ~= (ul2, nil A))).
    intros h n0. replace n0 with (n0 + 0).
    - intro tl1. intro H1. cut (tl ul1 ~= tl ul2).
      * intro Hcut. pose (IH' := IH _ _ Hcut); clearbody IH'.
        pose (f := fun n (x : Vector.t A n * Vector.t A 0) => let (v1, v2) := x in (cons A (hd ul1) n v1, v2)).
        cut (f _ (Ev.split (tl ul1)) ~= f _ (tl ul2, nil A)).
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

(*
Lemma tech_sem_not_exists d g tml Html s Hc ul1 (ul2 : Rel.T (length tml)) h :
  length s = length tml -> ul1 ~= ul2 ->
  SQLSem2.cond_sem d (s :: g)%list 
    (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s)) 
    Hc (Ev.env_app _ _ (Ev.env_of_tuple (s :: List.nil) ul1) h)
  = fold_right2 (fun (u0 v0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool)
      true (length tml) ul2 (Ev.v_tml_sem g tml Html h).
Proof.
(*
  intro Hlen. intro.
  eapply (bool_eq_P _ _ _ _ (fold_right_not_neq_iff (length tml) ul2 (Ev.v_tml_sem g tml Html h))). Unshelve.
  eapply (cond_sem_not_neq_iff _ _ _ _ Hlen). reflexivity.
  cut (list_sum (List.map (length (A:=Name)) (s :: Datatypes.nil)) = length tml).
  - intro Hcut1. cut (length s = 0 + list_sum (List.map (length (A:=Name)) (s :: Datatypes.nil))).
    * intro Hcut2. eapply (eq_is_subenv _ _ _ Hcut1 _ Hcut2 _ H). unfold is_subenv.
      intros. unfold Ev.var_sem.
      cut (forall HSome, Ev.unopt (Ev.env_lookup (s :: g) (Ev.env_app (s :: Datatypes.nil) g (Ev.env_of_tuple (s :: Datatypes.nil) ul1) h) (0, a)) HSome =
        nth ul1 (Fin.of_nat_lt Hk)).
      + intro Hcut; apply Hcut.
      + replace (Ev.env_lookup (s :: g) (Ev.env_app (s::List.nil) g (Ev.env_of_tuple (s :: List.nil) ul1) h) (0, a))
          with (Some (nth ul1 (Fin.of_nat_lt Hk))).
        ++ intro. reflexivity.
        ++ symmetry. simpl. replace (findpos s (fun x : Name => if Db.Name_dec x a then true else false) 0) with (Some k).
          -- simpl. transitivity (nth_error (to_list ul1) k).
            ** f_equal. apply to_list_eq.
              +++ simpl. omega.
              +++ eapply (@JMeq_trans _ _ _ _ (fst (ul2, Vector.nil Rel.V))).
                --- generalize ul2 H; clear ul2 H; rewrite <- Hlen; intros ul2 H. apply eq_JMeq.
                    f_equal. apply JMeq_eq. eapply split_n_0. exact H.
                --- simpl. symmetry. exact H.
            ** apply nth_error_Some_nth.
          -- symmetry. unfold Fin_findpos in H0. destruct (j_var_findpos a s Ha 0).
            destruct a0. simpl in H0. rewrite Fin.to_nat_of_nat in H0. simpl in H0.
            rewrite e. rewrite H0. f_equal. omega.
    * omega.
  - rewrite <- Hlen. simpl. omega.
Qed.

*)
*)

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
              ** contradiction.
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

  Lemma existT_eq_elim {A} {P : A -> Type} {a} {b} {p1} {p2} (e : existT P a p1 = existT P b p2) :
    forall (Q:Prop), (a = b -> p1 ~= p2 -> Q) -> Q.
  Proof.
    intros. injection e. intros _ H1. generalize dependent p2. generalize dependent p1. 
    rewrite H1. intros. apply H; auto. apply eq_JMeq. apply (existT_projT2_eq _ _ _ e).
  Qed.

  Lemma cast_JMeq S T U e x (y : U) : x ~= y -> cast S T e x ~= y.
  Proof.
    generalize dependent x. rewrite e. simpl. intuition.
  Qed.

  Lemma cast_elim {P:Prop} {A} (B : Type) (a : A) : A = B -> (forall (b:B), a ~= b -> P) -> P.
  Proof.
    intros; subst. apply (H0 _ JMeq_refl).
  Qed.

  Lemma S3_is_btrue_bneg : forall b, S3.is_btrue (S3.bneg b) = S3.is_bfalse b.
  Proof.
    intro. destr_tribool.
  Qed.

  Lemma S2_is_btrue_bneg : forall b, S2.is_btrue (S2.bneg b) = S2.is_bfalse b.
  Proof.
    intro. destruct b; auto.
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
    Ev.j_tml_sem g tml Stml ->
    monadic_map (fun val => val) (to_list (Stml h)) = Some x ->
    forall Sc, SQLSem2.j_cond_sem d g (List.fold_right (fun (t : pretm) (acc : precond) => 
      (t IS NOT NULL) AND acc) (TRUE) tml) Sc ->
    Sc h = true.
  Proof.
    intros Html Hmap.
    enough (forall t0 St0, List.In t0 tml -> Ev.j_tm_sem g t0 St0 -> exists v, St0 h = Some v).
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
          rewrite <- Hc. rewrite H0 in H. rewrite (Ev.j_tm_sem_fun _ _ _ H _ H1). reflexivity.
        * generalize dependent Hmap. apply bind_elim. Focus 2. intros. discriminate Hmap. 
          intros cl Hmap. intros. apply (IHHtml _ Hmap _ _ H0 H1).
  Qed.

  Lemma sem2_pred_false_aux' (d : D) (g : Ctx) tml Stml h :
    Ev.j_tml_sem g tml Stml ->
    monadic_map (fun val => val) (to_list (Stml h)) = @None (list BaseConst) ->
    forall Sc, SQLSem2.j_cond_sem d g (List.fold_right (fun (t : pretm) (acc : precond) => 
      (t IS NOT NULL) AND acc) (TRUE) tml) Sc ->
    Sc h = false.
  Proof.
    intros Html Hmap.
    cut (forall h t0 tml0 St0, Ev.j_tm_sem g t0 St0 -> St0 h = None -> List.In t0 tml0 -> 
      forall Sc0, SQLSem2.j_cond_sem d g (List.fold_right (fun t1 acc => 
      (t1 IS NOT NULL) AND acc) (TRUE) tml0) Sc0 -> Sc0 h = false).
    + intro Hcut. cut (exists t, List.In t tml /\ exists St, Ev.j_tm_sem g t St /\ St h = None).
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
          rewrite (Ev.j_tm_sem_fun _ _ _ H1 _ Ht0). rewrite Hnone. reflexivity.
        * rewrite (IH _ _ Ht0 Hnone H7 _ H4). apply Bool.andb_false_intro2. reflexivity.
  Qed.

  Lemma sem_bpred_tech : forall d G tml Stml h n p e,
    Ev.j_tml_sem G tml Stml ->
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

  Lemma fold_v_tml_sem1' g m tml Stml (Html : Ev.j_tml_sem g tml Stml) h Vl :
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

  Lemma cond_sem_cndeq_true2' d G t1 t2 Sc St1 St2 h :
    SQLSem2.j_cond_sem d G (cndeq t1 t2) Sc -> Sc h = true -> 
    Ev.j_tm_sem G t1 St1 -> Ev.j_tm_sem G t2 St2 ->
    exists k, St1 h = Some k /\ St2 h = Some k.
  Proof.
    intros Hc eSc Ht1 Ht2. inversion Hc. 
    apply (existT_eq_elim H2); intros; subst; clear H2.
    apply (existT_eq_elim H4); intros; subst; clear H4.
    clear H H5.
    eapply (Ev.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => _) _ H1). Unshelve. intros.
    apply (existT_eq_elim H5); intros; subst; clear H5 H6.
    eapply (Ev.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => _) _ H4). Unshelve. intros.
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
      - apply (Ev.j_tm_sem_fun _ _ _ Ht2 _ H3).
      - apply (Ev.j_tm_sem_fun _ _ _ Ht1 _ H2).
    + intros _ Hfalse. discriminate Hfalse.
  Qed.

  Lemma cond_sem_not_neq_iff' d g s tml (Hlen : length s = length tml) : 
    forall Stml Sc (ul : Rel.T (length tml)), 
    forall h h' h'', h = Ev.env_app (s::List.nil) _ h'' h' -> is_subenv' ul (Hlen : length s = 0 + length tml) h ->
    SQLSem2.j_cond_sem d (s :: g)%list 
      (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in 
        (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
        (TRUE) (combine tml s))
      Sc ->
    Ev.j_tml_sem g tml Stml -> 
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
      Ev.j_tml_sem g tml0 Stml ->
      Sc h  = true
      <-> (forall i, S3.is_bfalse (S3.veq (nth ul i) (nth (Stml h') i)) = false))
      _ _ _ _  Hlen List.nil eq_refl Hlen). Unshelve.
    + simpl. intros. split; intro.
      - intro. inversion i.
      - generalize h. inversion H2. intros. apply (existT_eq_elim H6). intros; subst. reflexivity.
    + simpl. intros x t s0 tml0 Hlen0 IH s1 Hs Hlens Stml0 Sc ul h h' h'' Happ Hsub Hc Html. split; intro.
      - intro i.
        cut (forall St, Ev.j_tm_sem g t St -> nth ul Fin.F1 = null \/ St h' = Db.null \/ St h' = nth ul Fin.F1).
        * generalize dependent Hsub.
          cut (forall i0 (ul1 : Rel.T (S (length tml0))), i0 ~= i -> ul1 ~= ul -> 
            is_subenv' ul1 Hlens h ->
            (forall St, Ev.j_tm_sem g t St -> nth ul1 Fin.F1 = null \/ St h' = null \/ St h' = nth ul1 Fin.F1) ->
            S3.is_bfalse (S3.veq (nth ul i0) (nth (Stml0 h') i)) = false). intro Hcut. apply Hcut. reflexivity. reflexivity.
          dependent inversion ul with (fun m (ul0 : Rel.T m) => forall i0 (ul1 : Rel.T (S (length tml0))),
            i0 ~= i -> ul1 ~= ul0 -> is_subenv' ul1 Hlens h ->
            (forall St, Ev.j_tm_sem g t St -> nth ul1 Fin.F1 = null \/ St h' = null \/ St h' = nth ul1 Fin.F1) ->
            S3.is_bfalse (S3.veq (nth ul0 i0) (nth (Stml0 h') i)) = false).
          intros i0 ul1 Hi0 Hul1; rewrite Hi0, Hul1; clear Hi0. intro Hsub.
          cut (exists St Stml1, Ev.j_tm_sem g t St /\ Ev.j_tml_sem g tml0 Stml1).
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
                eapply (Ev.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => forall h1, h1 ~= h' ->
                        cons _ (x0 h') _ (x1 h') ~= S' h1) _ Html). Unshelve. Focus 2.
               simpl. intros. apply (existT_eq_elim H8); intros; subst; clear H8. apply eq_JMeq.
               f_equal. rewrite (Ev.j_tm_sem_fun _ _ _ H2 _ H3). reflexivity.
               rewrite (Ev.j_tml_sem_fun _ _ _ H4 _ H5). reflexivity.
               apply H0. reflexivity.
          ++ eapply (Ev.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => 
                exists St Stml1, Ev.j_tm_sem g t St /\ Ev.j_tml_sem g tml0 Stml1) _ Html). Unshelve.
             simpl. intros. apply (existT_eq_elim H6); intros; subst; clear H6. exists St. exists Stml1.
             split. exact H2. exact H4.
        * generalize Hc, H. cut (forall h0, h0 ~= h -> SQLSem2.j_cond_sem d (s :: g)
            (((tmvar (0, x) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, x))))
              AND List.fold_right (fun (ta : pretm * Name) (acc : precond) => let (t0, a) := ta in
              ((tmvar (0, a) IS NULL) OR ((tm_lift t0 1 IS NULL) OR cndeq (tm_lift t0 1) (tmvar (0, a)))) AND acc)
             (TRUE) (combine tml0 s0)) Sc -> Sc h0 = true ->
            forall St, Ev.j_tm_sem g t St -> nth ul Fin.F1 = null \/ St h' = null \/ St h' = nth ul Fin.F1).
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
             assert (Hsuba : j_var x (s1 ++ x :: s0)). apply (Ev.j_var_sem_j_var _ _ _ H25).
             assert (Hsubk : 0 < S (length tml0)). omega.
             assert (Hfind : proj1_sig (Fin.to_nat (Fin_findpos x (s1 ++ x :: s0) Hsuba)) = 0 + length s1).
             rewrite (Fin_findpos_tech _ _ _ _ _ eq_refl). reflexivity.
             destruct (Hsub _ Hsuba _ Hsubk Hfind). destruct H1.
             replace (nth ul Fin.F1) with (nth ul (Fin.of_nat_lt Hsubk)). rewrite <- H2.
             rewrite (Ev.j_var_sem_fun _ _ _ H1 _ H25). unfold null. rewrite <- Hsem. reflexivity.
             reflexivity.
          ++ intro. eapply (S2_is_btrue_or_elim _ _ _ _ _ H0). Unshelve.
            -- intro. inversion H14. apply (existT_eq_elim H20); intros; subst; clear H20.
               pose (H10' := Ev.j_tm_sem_weak _ ((s1++x::s0)::List.nil) _ _ H10); clearbody H10'.
               rewrite (Ev.j_tm_sem_fun _ _ _ H18 _ H10') in H1. 
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
               assert (Hsuba : j_var x (s1 ++ x :: s0)). apply (Ev.j_var_sem_j_var _ _ _ H31). 
               assert (Hsubk : 0 < S (length tml0)). omega.
               assert (Hfind : proj1_sig (Fin.to_nat (Fin_findpos x (s1 ++ x :: s0) Hsuba)) = 0 + length s1).
               rewrite (Fin_findpos_tech _ _ _ _ _ eq_refl). reflexivity.
               destruct (Hsub _ Hsuba _ Hsubk Hfind). destruct H17.
               replace (nth ul Fin.F1) with (nth ul (Fin.of_nat_lt Hsubk)). rewrite <- H24.
               rewrite (Ev.j_var_sem_fun _ _ _ H17 _ H31).
               unfold Scm in H22. rewrite H22. rewrite <- H20.
               pose (H10' := Ev.j_tm_sem_weak _ ((s1++x::s0)::List.nil) _ _ H10); clearbody H10'.
               rewrite (Ev.j_tm_sem_fun _ _ _ H18 _ H10'). f_equal. apply Ev.env_eq. 
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
            -- cut (exists St0', Ev.j_tm_sem g t St0').
               ** intro Ht0'. destruct Ht0'. replace (St0 (Ev.env_app _ _ h'' h')) with (x0 h').
                  inversion H2. inversion H17. apply (existT_eq_elim H19); intros; subst; clear H19.
                  assert (Hsuba : j_var x (s1 ++ x :: s0)). apply (Ev.j_var_sem_j_var _ _ _ H22).
                  assert (Hsubk : 0 < S (length tml0)). omega.
                  assert (Hfind : proj1_sig (Fin.to_nat (Fin_findpos x (s1 ++ x :: s0) Hsuba)) = 0 + length s1).
                  rewrite (Fin_findpos_tech _ _ _ _ _ eq_refl). reflexivity.
                  destruct (Hsub _ Hsuba _ Hsubk Hfind). destruct H1. 
                  pose (H' := H Fin.F1). clearbody H'.
                  replace (nth ul Fin.F1) with (nth ul (Fin.of_nat_lt Hsubk)) in H'.
                  destruct (not_veq_false _ _ H').
                  +++ rewrite H15 in H13. rewrite (Ev.j_var_sem_fun _ _ _ H1 _ H22) in H13. unfold Scm in eSt. rewrite H13 in eSt. discriminate eSt.
                  +++ assert (forall h0 (f0 : Fin.t (length (t::tml0))), h0 ~= h' -> f0 ~= (Fin.F1 : Fin.t (length (t::tml0)))-> nth (Stml0 h0) f0 = x0 h').
                      eapply (Ev.j_tml_cons_sem _ _ _ _ (fun _ t' tml' S' =>
                        forall h0 (f0 : Fin.t (length (t'::tml'))), h0 ~= h' -> f0 ~= (Fin.F1 : Fin.t (length (t::tml0))) -> nth (S' h0) f0 = x0 h') _ Html).
                      Unshelve. Focus 2. intros. apply (existT_eq_elim H25); intros; subst; clear H25. simpl.
                      rewrite (Ev.j_tm_sem_fun _ _ _ H0 _ H19). reflexivity.
                      pose (H18' := (H18 h' Fin.F1 JMeq_refl JMeq_refl) : @nth Rel.V (S (@length pretm tml0)) (Stml0 h') (@Fin.F1 (@length pretm tml0)) = x0 h'); clearbody H18'.
                      rewrite H18' in H15. destruct H15. left. exact H15.
                      right. rewrite <- H15. rewrite <- H13.
                      rewrite (Ev.j_var_sem_fun _ _ _ H1 _ H22). reflexivity.
                  +++ reflexivity.
                  +++ pose (H0' := Ev.j_tm_sem_weak _ ((s1++x::s0)::List.nil) _ _ H0); clearbody H0'.
                      rewrite (Ev.j_tm_sem_fun _ _ _ H3 _ H0'). f_equal.
                      apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
                      transitivity (skipn (length (projT1 h'')) (projT1 h'' ++ projT1 h')).
                      rewrite Ev.skipn_append. reflexivity. f_equal. rewrite Ev.length_env. reflexivity.
               ** eapply (Ev.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => 
                    exists St0', Ev.j_tm_sem g t St0') _ Html). Unshelve.
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
            -- eapply (Ev.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' =>
                        Ev.j_tml_sem g' tml' (fun h0 => tl (S' h0))) _ Html). Unshelve.
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

  Theorem list_ind2 (A B : Type) (P : list A -> list B -> Type) :
      P List.nil List.nil ->
      (forall a al b bl, length al = length bl -> P al bl -> P (a::al) (b::bl)) ->
      forall al bl, length al = length bl -> P al bl.
  Proof.
    intros Hnil Hcons al. induction al.
    + intro. destruct bl; intuition. discriminate H.
    + intro. destruct bl; intuition. discriminate H.
  Qed.

(*
  Lemma veq_not_neq_cons hd1 hd2 n tl1 tl2 :
      S3.is_bfalse (S3.veq hd1 hd2) = false ->
      (forall i, S3.is_bfalse (S3.veq (nth tl1 i) (nth tl2 i)) = false) ->
      forall i, S3.is_bfalse (S3.veq (nth (cons _ hd1 n tl1) i) (nth (cons _ hd2 n tl2) i)) = false.
  Admitted.
*)

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

  Lemma tech_sem_cndeq d g t1 t2 Sc St1 St2 : 
    SQLSem2.j_cond_sem d g (cndeq t1 t2) Sc ->
    Ev.j_tm_sem g t1 St1 ->
    Ev.j_tm_sem g t2 St2 ->
    forall h, Sc h = S2.veq (St1 h) (St2 h).
  Proof.
    unfold cndeq. intros. inversion H. 
    apply (existT_eq_elim H5). intros; subst; clear H5 H8.
    apply (existT_eq_elim H7); intros; subst. clear H7 H2.
    inversion H4.
    apply (existT_eq_elim H6). intros; subst; clear H6 H8.
    inversion H7.
    apply (existT_eq_elim H8). intros; subst; clear H8 H10.
    rewrite (Ev.j_tm_sem_fun _ _ _ H5 _ H0). rewrite (Ev.j_tm_sem_fun _ _ _ H6 _ H1).
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

  Lemma tech_term_eq d g t a s1 al Sa St Sc h h0 x :
    Ev.j_tm_sem g t St ->
    Ev.j_tm_sem (((s1 ++ a:: List.nil) ++ al)::g) (tmvar (0,a)) Sa -> Sa (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h) = x ->
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
      assert (Ev.j_tm_sem ((((s1 ++ a :: List.nil) ++ al) :: List.nil) ++ g) (tm_lift t 1) (fun h => St (Ev.subenv2 h))).
        apply Ev.j_tm_sem_weak. exact H.
      rewrite (Ev.j_tm_sem_fun _ _ _ H3 _ H0).
      replace (Ev.subenv2 (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h)) with h.
        Focus 2. apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
        transitivity (skipn (length (projT1 h0)) (projT1 h0 ++ projT1 h)).
        rewrite Ev.skipn_append. reflexivity.
        f_equal. rewrite Ev.length_env. reflexivity.
      destruct H9.
      - replace (St0 (Ev.env_app _ _ h0 h)) with null. reflexivity.
        rewrite (Ev.j_tm_sem_fun _ _ _ H2 _ Ha). rewrite H1. reflexivity.
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
          rewrite (Ev.j_tm_sem_fun _ _ _ H2 _ Ha). rewrite H4.
          f_equal. symmetry. apply Db.BaseConst_eqb_eq. exact H8.
    + inversion H0. apply (existT_eq_elim H4); intros; subst; clear H0 H4 H7.
      inversion H5. apply (existT_eq_elim H4); intros; subst; clear H4 H5 H7.
      inversion H6. apply (existT_eq_elim H4); intros; subst; clear H4 H6 H8.
      inversion H5. apply (existT_eq_elim H6); intros; subst; clear H5 H6 H8.
      assert (Ev.j_tm_sem ((((s1 ++ a :: List.nil) ++ al) :: List.nil) ++ g) (tm_lift t 1) (fun h => St (Ev.subenv2 h))).
        apply Ev.j_tm_sem_weak. exact H.
      rewrite (Ev.j_tm_sem_fun _ _ _ H3 _ H0) in H9.
      replace (Ev.subenv2 (Ev.env_app (((s1 ++ a :: Datatypes.nil) ++ al) :: Datatypes.nil) g h0 h)) with h in H9.
        Focus 2. apply Ev.env_eq. unfold Ev.subenv2, Ev.env_app. simpl.
        transitivity (skipn (length (projT1 h0)) (projT1 h0 ++ projT1 h)).
        rewrite Ev.skipn_append. reflexivity.
        f_equal. rewrite Ev.length_env. reflexivity.
      unfold S2.bor, S2.of_bool in H9. eapply (bool_orb_elim _ _ _ _ _ H9). Unshelve.
      - destruct (St0 (Ev.env_app _ _ h0 h)) eqn:eSt0.
        * intro Hfalse. discriminate Hfalse.
        * intros _. left. unfold null. rewrite <- eSt0.
          rewrite (Ev.j_tm_sem_fun _ _ _ Ha _ H2). reflexivity.
      - apply bool_orb_elim.
        * destruct (St h) eqn:eSt. intro Hfalse; discriminate Hfalse. intros _. right. left. reflexivity.
        * replace (Sc0 (Ev.env_app _ _ h0 h)) with (S2.veq (St h) (St0 (Ev.env_app _ _ h0 h))).
          unfold S2.veq. destruct (St h) eqn:eSt.
          ++ destruct (St0 (Ev.env_app _ _ h0 h)) eqn:eSt0.
            -- intro. right. right. exists b. exists b0. intuition.
               rewrite (Ev.j_tm_sem_fun _ _ _ Ha _ H2). rewrite eSt0. 
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

  Lemma cons_equal {A} : forall h1 h2 n1 n2 t1 t2,
    h1 = h2 -> n1 = n2 -> t1 ~= t2 -> cons A h1 n1 t1 ~= cons A h2 n2 t2.
  Proof.
    intros. generalize t1 t2 H1; clear t1 t2 H1. rewrite H, H0.
    intros. rewrite H1. reflexivity.
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

  Lemma tech_vec_append_tmvar : forall a s1 s2 (x:Rel.T (S (length s2))) (y:Rel.T (length s1)) e g h,
    forall Sa,
    Ev.j_tm_sem ((s1++a::s2)::g) (tmvar (0,a)) Sa ->
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

  Lemma tech_sem_not_exists' d g tml s ul1 (ul2 : Rel.T (length tml)) Sc Stml h :
    length s = length tml -> ul1 ~= ul2 ->
    SQLSem2.j_cond_sem d (s :: g)%list 
      (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s)) 
      Sc ->
    Ev.j_tml_sem g tml Stml ->
    Sc (Ev.env_app _ _ (Ev.env_of_tuple (s :: List.nil) ul1) h)
    = fold_right2 (fun (u0 v0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool)
        true (length tml) ul2 (Stml h).
(*
  Lemma tech_j_cond_fold_vect' d s0 n (s : Vector.t Name n) g (tml : Vector.t pretm n) :
    List.NoDup s0 -> forall Stml, Ev.j_tml_sem g (to_list tml) Stml -> incl (to_list s) s0 ->
    exists Sc : Ev.env ((s0 :: Datatypes.nil) ++ g) -> S2.B,
    SQLSem2.j_cond_sem d ((s0 :: Datatypes.nil) ++ g)
      (List.fold_right
       (fun (ta : pretm * Name) (acc : precond) =>
        let (t, a) := ta in
        ((tmvar (0, a) IS NULL) OR ((tm_lift t 1 IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a)))) AND acc) 
       (TRUE) (combine (VectorDef.to_list tml) (VectorDef.to_list s))) Sc.
  Proof.

    eapply (Vector.rect2 (fun n s' tml' => 
      forall Stml, Ev.j_tml_sem g (to_list tml') Stml -> incl (to_list s') s0 -> 
      exists Sc,
      SQLSem2.j_cond_sem d ((s0 :: List.nil) ++ g) (List.fold_right
        (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
        (combine (to_list tml') (to_list s'))) Sc)
      _ _ s tml). Unshelve.*)
  Proof.
    intros Hlen Heq Hc Html.
    enough 
      (forall s1, 
         forall ul1 ul2 (ul0 : Rel.T (length s1)), ul1 ~= Vector.append ul0 ul2 -> 
         forall Stml, Ev.j_tml_sem g tml Stml -> 
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
        forall Stml, Ev.j_tml_sem g tml0 Stml -> 
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
      reflexivity. assert (Ha : exists Sa, Ev.j_tm_sem (((s1 ++ a :: Datatypes.nil) ++ al) :: g) (tmvar (0,a)) Sa).
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

(*
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
*)

  Lemma cond_sem_not_ex_selstar' d g q s s0 tml Hs0 (Hlens : length s = length s0) 
     Sff Sq Sc (Hff : SQLSem2.j_cond_sem d g (NOT (EXISTS (SELECT * FROM (tbquery (ttquery d q), s0) :: Datatypes.nil
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
    inversion H2. apply (existT_eq_elim H8); intros; subst. clear H2 H8 H5 H11. 
    apply (existT_eq_elim (JMeq_eq H12)); intros; subst. clear H12 H.
    eapply (SQLSem2.j_nil_btb_sem _ _ _ _ _ _ H9). Unshelve. intros; subst. rewrite <- H2. clear H9 H2.
    inversion H7. apply (existT_eq_elim H2); intros; subst. clear H7 H2 H4.
    apply (existT_eq_elim (JMeq_eq H5)); intros; subst. clear H5 H.
    transitivity (0 <?
      Rel.card
        (Rel.sel
           (cast (Rel.R (length s1 + list_sum (List.map (length (A:=Name)) Datatypes.nil)))
              (Rel.R (length s0 + list_sum (List.map (length (A:=Name)) Datatypes.nil))) e
              (Rel.times (ST h) Rel.Rone))
           (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) (s0 :: Datatypes.nil))) =>
            S2.is_btrue (Sc0 (Ev.env_app (s0 :: Datatypes.nil) g (Ev.env_of_tuple (s0 :: Datatypes.nil) Vl) h))))).
    reflexivity. f_equal. apply eq_card_dep. rewrite Hlens. simpl. omega.
    eapply (f_JMequal (Rel.sel _) (Rel.sel _)).
    eapply (f_JMequal (@Rel.sel _) (@Rel.sel _)). rewrite Hlens. simpl. rewrite plus_0_r. reflexivity.
    destruct (SQLSem2.jq_sem_fun_dep _ _ _ _ _ Hq _ _ _ _ eq_refl eq_refl H3). subst.
    apply cast_JMeq. symmetry. apply p_ext_dep. simpl. omega.
    intros. replace r2 with (Vector.append r1 (Vector.nil _)).
    rewrite (Rel.p_times _ _ _ _ _ r1 (nil _) eq_refl). rewrite Rel.p_one. rewrite H0. omega.
    apply JMeq_eq. eapply (JMeq_trans (vector_append_nil_r r1)). exact H.
    apply fun_ext_dep. rewrite Hlens. simpl. rewrite plus_0_r. reflexivity.
    intros Vl1 Vl2 HVl. unfold S2.is_btrue. apply JMeq_eq. eapply (f_JMequal (eb:=JMeq_refl) Sc0 Sc).
    eapply (SQLSem2.jc_sem_fun_dep _ _ _ _ H6 _ _ _ _ _ Hc).
    eapply (f_JMequal (Ev.env_app _ _ _) (Ev.env_app _ _ _)).
    eapply (f_JMequal (Ev.env_app _ _) (Ev.env_app _ _)). reflexivity.
    eapply (f_JMequal (Ev.env_of_tuple _) (Ev.env_of_tuple _)). reflexivity.
    symmetry. apply cast_JMeq. symmetry. exact HVl. reflexivity.
    Unshelve.
    simpl. rewrite plus_0_r. rewrite Hlens. reflexivity.
    simpl. rewrite plus_0_r. rewrite Hlens. reflexivity.
    simpl. rewrite plus_0_r. rewrite Hlens. reflexivity.
    simpl. rewrite plus_0_r. rewrite Hlens. reflexivity.
    reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
    reflexivity. reflexivity.
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
    List.NoDup s0 -> forall Stml, Ev.j_tml_sem g (to_list tml) Stml -> incl (to_list s) s0 ->
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
      forall Stml, Ev.j_tml_sem g (to_list tml') Stml -> incl (to_list s') s0 -> 
      exists Sc,
      SQLSem2.j_cond_sem d ((s0 :: List.nil) ++ g) (List.fold_right
        (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) 
        (combine (to_list tml') (to_list s'))) Sc)
      _ _ s tml). Unshelve.
    + simpl. intros. eexists. constructor. 
    + simpl. intros m s' tml' IH a0 t0 Stml Html' Hincl.
      unfold to_list in Html'. 
      eapply (Ev.j_tml_cons_sem _ _ _ _ (fun g' t' tml' S' => _) _ Html'). Unshelve. simpl. intros.
      apply (existT_eq_elim H3); intros; subst; clear H3 H5.
      enough (incl (to_list s') s0). destruct (IH _ H4 H0).
      enough (exists Sa0, Ev.j_var_sem s0 a0 Sa0). destruct H3.
      eexists. constructor. Focus 2. exact H1.
      constructor. constructor. constructor. constructor. exact H3.
      constructor. constructor. eapply (Ev.j_tm_sem_weak g (s0::List.nil) _ _ H2).
      constructor. constructor. eapply (Ev.j_tm_sem_weak g (s0::List.nil) _ _ H2).
      constructor. constructor. constructor. exact H3. constructor.
      apply tech_j_var_sem. apply Hincl. left. reflexivity. exact Hnodup.
      intros x Hx. apply Hincl. right. exact Hx.
      Unshelve. reflexivity.
  Qed.

  Lemma tech_j_cond_fold' d s0 s g tml :
    length tml = length s -> List.NoDup s0 -> forall Stml, Ev.j_tml_sem g tml Stml-> incl s s0 ->
    exists Sc,
    SQLSem2.j_cond_sem d ((s0 :: Datatypes.nil) ++ g) (List.fold_right
     (fun (ta : pretm * Name) (acc : precond) => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc)
     (TRUE) (combine tml s)) Sc.
  Proof.
    intro Hlen. rewrite <- (to_list_of_list_opp tml). rewrite <- (to_list_of_list_opp s).
    generalize (of_list tml) (of_list s). rewrite Hlen. intros vtml vs. apply tech_j_cond_fold_vect'.
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
          (fun G0 Q0 S0 _ => exists S1, SQLSem2.j_in_q_sem d G0 (ttquery d Q0) S1 /\ forall h, S0 h ~= S1 h)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
  Unshelve.
  (** mutual induction cases: query *)
  + simpl. intros G0 b tml btb c G1 Sbtb Sc Stml e Hbtb IHbtb Hc IHc Html.
    decompose record IHbtb. decompose record IHc.
    eexists. split. eapply (SQLSem2.jqs_sel _ _ _ _ _ _ _ _ _ _ e H1 H0 Html).
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
  + simpl. intros G0 b btb c G1 Sbtb Sc Stml e Hbtb IHbtb Hc IHc Html.
    decompose record IHbtb. decompose record IHc.
    eexists. split. eapply (SQLSem2.jqs_selstar _ _ _ _ _ _ _ _ _ e H1 H0 Html).
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
    split. constructor. exact Ht. split. constructor. exact Ht.
    split; intros; destruct (St h); destruct b; reflexivity. 
  + simpl. intros G0 n p tml Stml e Html.
    cut (exists Sc2, SQLSem2.j_cond_sem d G0 (List.fold_right (fun (t : pretm) (acc : precond) => 
      (t IS NOT NULL) AND acc) (TRUE) tml) Sc2).
    intro Hc2. decompose record Hc2. clear Hc2. eexists. eexists.
    split. eapply (SQLSem2.jcs_pred _ _ _ _ _ _ e). Unshelve. exact Html.
    split. constructor. Unshelve. constructor. Unshelve. constructor. Unshelve. exact Html.
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
    - intro. erewrite <- (sem_bpred_tech _ _ _ _ _ _ _ _ Html). reflexivity. exact H0.
    - elim Html.
      * simpl. eexists. constructor.
      * intros t0 tml0 St0 Stml0 Ht0 Html0 IH. destruct IH. simpl. eexists. constructor.
        constructor. exact Ht0. exact H0. 
  + hnf. intros G0 b tml q s0 Stml Sq e Html Hq IHq.
    decompose record IHq. destruct b.
    - cut (exists S2, SQLSem2.j_cond_sem d G0 (ffcond d (tml IN q)) S2).
      * intro Hff. decompose record Hff. clear Hff.
        eexists. exists x0. split. constructor. exact Html. exact H1. split.
        exact H0. split.
        ++ intro h. simpl.        
          destruct (0 <? Rel.card (Rel.sel (Sq h)
           (fun rl : Rel.T (length s0) =>
            fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
            (length s0) rl (cast _ _ (f_equal Rel.T e) (Stml h))))) eqn:e0.
          -- transitivity true. reflexivity. symmetry. apply if_true.
            ** eapply (trans_eq _ e0). Unshelve. exact e. 
               rewrite (fold_v_tml_sem1' _ _ _ _ Html h).
               rewrite H2. reflexivity. apply cast_JMeq. reflexivity.
            ** reflexivity.
          -- transitivity false.
            ** destruct (0 <? Rel.card (Rel.sel (Sq h)
               (fun rl : Rel.T (length s0) => fold_right2 (fun (r0 V0 : Value) (acc : bool) => 
                 (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool) true (length s0) rl (cast _ _ (f_equal Rel.T e) (Stml h)))));
             reflexivity.
            ** symmetry. apply if_false.
              +++ rewrite <- e0. rewrite (fold_v_tml_sem1' _ _ _ _ Html h).
               rewrite H2. reflexivity. apply cast_JMeq. reflexivity.
              +++ apply if_elim; reflexivity.
        ++ intro. rewrite H2. simpl in H0. pose (s1 := freshlist (length tml)).
           cut (exists Sc, SQLSem2.j_cond_sem d (s1 :: G0)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s1)) Sc).
           intro Hcut. Focus 2. eapply tech_j_cond_fold'.
           symmetry. apply length_freshlist. apply p_freshlist. exact Html. intro. intuition.
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
                exact H3. exact Html. Unshelve.
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
                    exact H3. exact Html. Unshelve.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
                    rewrite e; reflexivity.
          -- symmetry. rewrite e. apply length_freshlist.
      * destruct (tech_j_cond_fold' d (freshlist (length tml)) (freshlist (length tml)) G0 _ 
            (eq_sym (length_freshlist _)) (p_freshlist _) _ Html (fun x Hx => Hx)).
        eexists. constructor. constructor. constructor. constructor. constructor. exact H1.
        constructor. rewrite length_freshlist. symmetry. exact e. exact H0.
        Unshelve. simpl. repeat rewrite plus_0_r. rewrite length_freshlist. rewrite e. reflexivity.
    - cut (exists S1, SQLSem2.j_cond_sem d G0 (ttcond d (tml NOT IN q)) S1).
      * intro Htt. decompose record Htt. clear Htt. exists x0.
        eexists. split. exact H0. split. constructor. exact Html. exact H1. split.
        ++ intro. rewrite H2. simpl in H0. pose (s1 := freshlist (length tml)).
           cut (exists Sc, SQLSem2.j_cond_sem d (s1 :: G0)%list
                       (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) 
                          (TRUE) (combine tml s1)) Sc).
           intro Hcut. Focus 2. eapply tech_j_cond_fold'.
           symmetry. apply length_freshlist. apply p_freshlist. exact Html. intro. intuition.
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
                exact H3. exact Html. Unshelve.
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
                    exact H3. exact Html. Unshelve.
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
            ** rewrite <- e0 at 1. rewrite (fold_v_tml_sem1' _ _ _ _ Html h). rewrite H2. reflexivity.
               apply cast_JMeq. reflexivity.
            ** reflexivity.
          -- transitivity false.
            ** destruct (0 <? Rel.card (Rel.sel (Sq h)
               (fun rl : Rel.T (length s0) => fold_right2 (fun (r0 V0 : Value) (acc : bool) => 
                 (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool) true (length s0) rl (cast _ _ (f_equal Rel.T e) (Stml h)))));
             reflexivity.
            ** symmetry. apply if_false.
              +++ rewrite <- e0. rewrite (fold_v_tml_sem1' _ _ _ _ Html h). 
                  decompose record IHq. destruct (SQLSem2.jq_sem_fun_dep _ _ _ _ _ H4 _ _ _ _ eq_refl eq_refl H1).
                  rewrite H6 in H5. rewrite H5. reflexivity.
                  apply cast_JMeq. reflexivity.
              +++ apply if_elim; reflexivity.
      * destruct (tech_j_cond_fold' d (freshlist (length tml)) (freshlist (length tml)) G0 _ 
            (eq_sym (length_freshlist _)) (p_freshlist _) _ Html (fun x Hx => Hx)).
        eexists. constructor. constructor. constructor. constructor. constructor. exact H1.
        constructor. rewrite length_freshlist. symmetry. exact e. exact H0.
        Unshelve. simpl. repeat rewrite plus_0_r. rewrite length_freshlist. rewrite e. reflexivity.
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
  (** mutual induction cases: inquery *)
  + simpl. intros G0 b tml btb c G1 Sbtb Sc Stml Hbtb IHbtb Hc IHc Html.
    decompose record IHbtb. decompose record IHc.
    eexists. split. eapply (SQLSem2.jiqs_sel _ _ _ _ _ _ _ _ _ _ H1 H0 Html).
    intro. simpl. destruct b.
    - apply eq_JMeq. f_equal. f_equal. f_equal. apply JMeq_eq. rewrite H2.
      eapply (f_JMequal (Rel.sum _) (Rel.sum _)). Unshelve.
      eapply (f_JMeq _ _ (@Rel.sum _ _)). apply JMeq_eq. eapply (f_JMeq _ _ (Rel.sel _)).
      extensionality Vl. rewrite H4. reflexivity.
      reflexivity. exact e. reflexivity. reflexivity.
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