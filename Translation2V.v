Require Import Eqdep Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool 
  Semantics JMeq FunctionalExtensionality Omega Coq.Init.Specif.

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
    + intros. reflexivity.
    + intros. reflexivity.
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
               (existT (fun h1 : Ev.preenv => length s0 :: Datatypes.nil = List.map (length (A:=Value)) h1)
                  (to_list (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl)))
                   :: Datatypes.nil)
                  (eq_ind_r (fun n : nat => length s0 :: Datatypes.nil = n :: Datatypes.nil) eq_refl
                     (length_to_list Rel.V (length s0)
                        (fst (Ev.split (cast (Rel.T (length s)) (Rel.T (length s0 + 0)) Hs0 Vl))))))
               (existT (fun h1 : Ev.preenv => Datatypes.nil = List.map (length (A:=Value)) h1) Datatypes.nil
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
  pose (p := fun ul0 => fold_right2 (fun u0 v0 acc => (acc && S3.is_btrue (S3.veq u0 v0))%bool) true n ul0 vl).
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

Lemma list_In_vec_In {A} (a : A) (l : list A) : List.In a l -> Vector.In a (Vector.of_list l).
Proof.
  elim l.
  + intro H. contradiction H.
  + intros a0 l0 IH H. destruct H.
    - rewrite H. constructor.
    - constructor. apply IH. exact H.
Qed.

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

Definition Fin_findpos a s (Ha : j_var a s) : Fin.t (length s).
  refine (@Fin.of_nat_lt (projT1 (j_var_findpos a s Ha 0)) _ _).
  destruct (projT2 (j_var_findpos a s Ha 0)). exact H.
Defined.

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

Lemma Fin_findpos_tech a s Ha : forall s1 s2, s = s1 ++ a :: s2 -> 
  proj1_sig (Fin.to_nat (Fin_findpos a s Ha)) = length s1.
Proof.
  elim Ha.
  + intros. simpl. replace s1 with (@List.nil Name). reflexivity.
    generalize s0 s2 n H; clear s0 n s2 H. elim s1.
    - intros. reflexivity.
    - simpl. intros a0 l IH s0 s2 H e. injection e. intros.
      rewrite H0 in H. contradiction H. apply in_or_app. right. left. reflexivity.
  + intros. simpl. destruct s1; simpl in H0; injection H0; intros.
    - contradiction n. auto.
    - simpl. transitivity (S (proj1_sig (Fin.to_nat (Fin_findpos a s0 j)))).
      * simpl. unfold Fin_findpos. 
        ++ destruct (j_var_findpos a (b :: s0) (j_varcons a b s0 n j) 0).
          destruct a0.
          destruct (j_var_findpos a s0 j 0). destruct a0. simpl.
          repeat rewrite Fin.to_nat_of_nat. simpl.
          simpl in e. destruct (Db.Name_dec b a).
          ** contradiction n. auto.
          ** rewrite (findpos_m_Some_step _ _ _ _ _ e0) in e.
            injection e. auto.
      * f_equal. eapply H. exact H1.
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
    - generalize h. dependent inversion Hc. intros. reflexivity.
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

Lemma tech_sem_not_exists d g tml Html s Hc ul1 (ul2 : Rel.T (length tml)) h :
  length s = length tml -> ul1 ~= ul2 ->
  SQLSem2.cond_sem d (s :: g)%list 
    (List.fold_right (fun (ta : pretm * Name) acc => let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s)) 
    Hc (Ev.env_app _ _ (Ev.env_of_tuple (s :: List.nil) ul1) h)
  = fold_right2 (fun (u0 v0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq u0 v0)))%bool)
      true (length tml) ul2 (Ev.v_tml_sem g tml Html h).
Proof.
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

  Theorem sem_bool_to_tribool : forall d G Q s HWF,
    exists HWF1, forall h,
    SQLSem3.q_sem d G Q s HWF h ~= SQLSem2.q_sem d G (ttquery d Q) s HWF1 h.
  intros d G Q s HWF.
  eapply (jq_ind_mut _ 
          (fun G0 Q0 s0 H0 => exists HWF1, forall h,
            SQLSem3.q_sem d G0 Q0 s0 H0 h ~= SQLSem2.q_sem d G0 (ttquery d Q0) s0 HWF1 h)
          (fun G0 T0 s0 H0 => exists HWF1, forall x h,
            SQLSem3.tb_sem d G0 x T0 s0 H0 h ~= SQLSem2.tb_sem d G0 x (tttable d T0) s0 HWF1 h)
          (fun G0 c0 H0 => exists HWF1 HWF2, 
            (forall h, S3.is_btrue (SQLSem3.cond_sem d G0 c0 H0 h) = S2.is_btrue (SQLSem2.cond_sem d G0 (ttcond d c0) HWF1 h)) /\
            (forall h, S3.is_btrue (negtb (SQLSem3.cond_sem d G0 c0 H0 h)) = S2.is_btrue (SQLSem2.cond_sem d G0 (ffcond d c0) HWF2 h)))
          (fun G0 btb G1 H0 => exists HWF1, forall h,
            SQLSem3.btb_sem d G0 btb G1 H0 h ~= SQLSem2.btb_sem d G0 (List.map (fun bT => (tttable d (fst bT), snd bT)) btb) G1 HWF1 h) 
          (fun G0 Q0 H0 => exists HWF1, forall h,
            SQLSem3.inner_q_sem d G0 Q0 H0 h ~= SQLSem2.inner_q_sem d G0 (ttquery d Q0) HWF1 h)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF).
  Unshelve.
  (** mutual induction cases: j_query *)
  + intros s0 c b btm btb g g1 Hbtb IHbtb Hcond IHcond Html e. rewrite e. clear e s0.
    case IHbtb. clear IHbtb. intros Hbtb' IHbtb.
    case IHcond. clear IHcond. intros Hcond' IHcond.
    case IHcond. clear IHcond. intros Hcond'' IHcond.
    case IHcond. clear IHcond. intros IHcond _. clear Hcond''.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_select. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl. 
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. reflexivity.
  + intros g btb g1 c s0 b Hbtb IHbtb Hcond IHcond e Html. rewrite e. clear e s0.
    case IHbtb. clear IHbtb. intros Hbtb' IHbtb.
    case IHcond. clear IHcond. intros Hcond' IHcond.
    case IHcond. clear IHcond. intros Hcond'' IHcond.
    case IHcond. clear IHcond. intros IHcond _. clear Hcond''.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_selstar. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. f_equal. f_equal. f_equal.
      * f_equal. f_equal. f_equal.
        extensionality Vl. rewrite IHcond.
        reflexivity.
      * f_equal. f_equal. f_equal. f_equal.
        extensionality Vl. rewrite IHcond.
        reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. f_equal. f_equal. f_equal.
      * f_equal. f_equal. f_equal.
        extensionality Vl. rewrite IHcond.
        reflexivity.
      * f_equal. f_equal. f_equal. f_equal.
        extensionality Vl. rewrite IHcond.
        reflexivity.
  + intros g b q1 q2 s0 Hq1 IHq1 Hq2 IHq2.
    case IHq1. clear IHq1. intros Hq1' IHq1.
    case IHq2. clear IHq2. intros Hq2' IHq2.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_union. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_plus. rewrite Rel.p_plus.
      rewrite IHq1, IHq2. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_plus. rewrite Rel.p_plus.
      rewrite IHq1, IHq2. reflexivity.
  + intros g b q1 q2 s0 Hq1 IHq1 Hq2 IHq2.
    case IHq1. clear IHq1. intros Hq1' IHq1.
    case IHq2. clear IHq2. intros Hq2' IHq2.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_inters. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_inter. rewrite Rel.p_inter.
      rewrite IHq1, IHq2. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_inter. rewrite Rel.p_inter.
      rewrite IHq1, IHq2. reflexivity.
  + intros g b q1 q2 s0 Hq1 IHq1 Hq2 IHq2.
    case IHq1. clear IHq1. intros Hq1' IHq1.
    case IHq2. clear IHq2. intros Hq2' IHq2.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_except. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_minus. rewrite Rel.p_minus.
      rewrite IHq1, IHq2. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_minus. rewrite Rel.p_minus.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite IHq1, IHq2. reflexivity.
  (** mutual induction cases: j_tb *)
  + intros x s0 g Hdb e. eexists. Unshelve. Focus 2. constructor 1. all: eauto.
    intros b h. simpl. repeat rewrite eq_rect_r_eq_refl. reflexivity.
  + intros g q s0 Hq IHq. 
    case IHq. clear IHq. intros Hq' IHq'.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_tbquery. assumption.
    intros b h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite IHq'. reflexivity.
  (** mutual induction cases: j_cond *)
  + intros g Hdb. 
    eexists. Unshelve. Focus 2. apply j_cndtrue. assumption.
    eexists. Unshelve. Focus 2. apply j_cndfalse. assumption. split; intro h; reflexivity.
  + intros g Hdb. 
    eexists. Unshelve. Focus 2. apply j_cndfalse. assumption.
    eexists. Unshelve. Focus 2. apply j_cndtrue. assumption. split; intro h; reflexivity.
  + intros g t b Hdb Ht. 
    eexists. Unshelve. Focus 2. apply j_cndnull. all:eauto.
    eexists. Unshelve. Focus 2. apply j_cndnull. all:eauto. split.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
      destruct (Ev.tm_sem g t Ht h); destruct b; reflexivity.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
      case (Ev.tm_sem g t Ht h); destruct b; simpl; auto.
  + intros g n p tml Hdb Html e. generalize p; clear p. rewrite <- e. intro p.
    eexists. Unshelve. Focus 2.
    simpl. apply j_cndpred. all:eauto.
    eexists. Unshelve. Focus 2.
    simpl. apply j_cndand.
    apply j_cndnot. apply j_cndpred. all:eauto.
    generalize Html. clear Html. elim tml;simpl.
    intro. constructor. exact Hdb.
    intros hd tl IH H. constructor.
    constructor. exact Hdb.
    eapply H. simpl. auto.
    apply IH. intros x Htl. eapply H. right. exact Htl.
    split; intro h.
    - simpl. repeat rewrite eq_rect_r_eq_refl. apply S3.sem_bpred_elim.
      * apply S2.sem_bpred_elim.
        ++ intros. rewrite H in H0. injection H0. intro. generalize Hcl0; clear Hcl0. rewrite <- H1.
           intro Hcl0. replace (p cl Hcl0) with (p cl Hcl). 
           -- destruct (p cl Hcl); reflexivity.
           -- f_equal. apply EqdepTheory.UIP.
        ++ intros H1 cl. rewrite H1. intro Hfalse. discriminate Hfalse.
      * apply S2.sem_bpred_elim.
        ++ intros cl H1. rewrite H1. intros Hcl Hfalse. discriminate Hfalse.
        ++ intros. reflexivity.
    - cut (forall j1, S3.is_btrue (S3.bneg (SQLSem3.cond_sem d g (cndpred (length tml) p tml) (j_cndpred d g (length tml) p tml Hdb Html eq_refl) h)) = 
          S2.is_btrue (S2.band (S2.bneg (SQLSem2.cond_sem d g (cndpred (length tml) p tml) (j_cndpred d g (length tml) p tml Hdb Html eq_refl) h)) 
          (SQLSem2.cond_sem d g (List.fold_right (fun t acc => cndand (cndnull false t) acc) cndtrue tml) j1 h))).
      intro Hcut; apply Hcut.
      destruct (SQLSem3.cond_sem d g (cndpred (length tml) p tml) (j_cndpred d g (length tml) p tml Hdb Html eq_refl) h) eqn:e0.
      * destruct (sem3_pred_ttrue _ _ _ _ _ _ _ _ _ e0). destruct H.
        simpl. repeat rewrite eq_rect_r_eq_refl. symmetry.
        apply S2.sem_bpred_elim.
        ++ intros. apply S2_is_btrue_false_and1. destruct H.
           rewrite H in H0. replace (p cl Hcl) with (p x x0). rewrite H1. reflexivity.
           injection H0. intro. generalize Hcl. clear Hcl. rewrite <- H2. intro.
           f_equal. apply EqdepTheory.UIP.
        ++ destruct H. rewrite H. intro Hfalse. discriminate Hfalse.
      * destruct (sem3_pred_tfalse _ _ _ _ _ _ _ eq_refl _ e0).
        simpl. repeat rewrite eq_rect_r_eq_refl. symmetry.
        destruct H. destruct H. apply S2_is_btrue_and_intro.
        ++ apply S2.sem_bpred_elim.
           -- rewrite H. intros. injection H1. intro. generalize Hcl; clear Hcl. rewrite <- H2. intro.
              replace (p x Hcl) with (p x x0). rewrite H0. reflexivity.
              f_equal. apply EqdepTheory.UIP.
           -- rewrite H. intro Hfalse. discriminate Hfalse.
        ++ rewrite (sem2_pred_true_aux _ _ _ _ _ _ _ H). reflexivity.
      * simpl. symmetry. repeat rewrite eq_rect_r_eq_refl. apply S2_is_btrue_false_and2.
        rewrite (sem2_pred_false_aux _ _ _ _ _ _ (sem3_pred_unknown _ _ _ _ _ _ _ _ _ e0)). reflexivity.
  + intros g q s0 tml b Html Hq IHq e.
    case IHq. clear IHq. intros Hq' IHq. destruct b.
    - eexists. Unshelve. Focus 2. eapply j_cndmemb. all:eauto.
      cut (j_cond d g (ffcond d (tml IN q))).
      * intro Hff. exists Hff. split.
        ++ intro h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite IHq.
           destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
            (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e) (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
            (fun rl : Rel.T (length tml) =>
              fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
              (length tml) rl (Ev.v_tml_sem g tml Html h)))) eqn:e0.
           -- transitivity true. reflexivity. symmetry. apply if_true.
              ** rewrite <- e0. rewrite fold_v_tml_sem1. reflexivity.
              ** reflexivity.
           -- transitivity false.
              ** destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
                    (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e)
                    (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
                   (fun rl : Rel.T (length tml) => fold_right2 (fun (r0 V0 : Value) (acc : bool) => 
                    (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool) true (length tml) rl 
                    (Ev.v_tml_sem g tml Html h))));reflexivity.
              ** symmetry. apply if_false.
                 +++ rewrite <- e0. rewrite fold_v_tml_sem1. reflexivity.
                 +++ apply if_elim; reflexivity.
        ++ intro h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite IHq. simpl in Hff.
           pose (s1 := freshlist (length tml)).
           assert (j_cond d (s1 :: g) (List.fold_right (fun (ta : pretm * Name) acc =>
              let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s1))).
           -- inversion Hff. inversion X. inversion X0. inversion X1. inversion X4. inversion X3. subst.
              exact X2.
           -- assert (HlenT : Rel.T (length s0) = Rel.T (list_sum (List.map (length (A:=Name)) (s1 :: Datatypes.nil)))).
              simpl. f_equal. unfold s1. rewrite plus_0_r. rewrite length_freshlist. exact e.
              erewrite (cond_sem_not_ex_selstar _ _ _ _ _ Hq' _ _ _ _ X). Unshelve.
              Focus 2. exact HlenT.
              f_equal.
              destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
                    (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e)
                    (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
                 (fun rl : Rel.T (length tml) => fold_right2
                  (fun (r0 V0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool)
                  true (length tml) rl (Ev.v_tml_sem g tml Html h)))) eqn:e1.
              ** transitivity false.
                 destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
                      (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e) 
                      (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
                  (fun rl : Rel.T (length tml) => fold_right2
                   (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
                   (length tml) rl (Ev.v_tml_sem g tml Html h)))); reflexivity.
                 symmetry. transitivity (negb true); try reflexivity.
                 rewrite <- e1 at 1. f_equal. f_equal. apply eq_card_dep; auto.
                 apply eq_sel; auto.
                 +++ rewrite <- e. intros. rewrite H. reflexivity.
                 +++ intros. apply tech_sem_not_exists. unfold s1. rewrite length_freshlist. reflexivity.
                    generalize r1 r2 H; clear r1 r2 H.
                    rewrite <- e. intros. rewrite H.
                    generalize HlenT; clear HlenT.
                    simpl. unfold s1. rewrite length_freshlist. rewrite <- e. rewrite plus_0_r.
                    intro HlenT. rewrite (UIP_refl _ _ HlenT). reflexivity.
              ** transitivity true.
                 +++ apply if_false; auto.
                     generalize e1; clear e1. apply bool_contrapos.
                     intro. apply Nat.ltb_lt in H. apply Nat.ltb_lt.
                     apply (lt_le_trans _ _ _ H). apply le_card_eq_not_neq.
                 +++ symmetry. transitivity (negb false); try reflexivity. f_equal.
                     rewrite <- e1. f_equal. apply eq_card_dep; auto.
                     apply eq_sel; auto.
                     --- rewrite <- e. intros. rewrite H. reflexivity.
                     --- intros. apply tech_sem_not_exists. unfold s1. apply length_freshlist.
                         generalize r1 r2 H; clear r1 r2 H.
                         rewrite <- e. intros. rewrite H.
                         generalize HlenT; clear HlenT.
                         simpl. unfold s1. rewrite length_freshlist. rewrite <- e. rewrite plus_0_r.
                         intro HlenT. rewrite (UIP_refl _ _ HlenT). reflexivity.
              ** unfold s1. rewrite length_freshlist. rewrite e. reflexivity.
      * simpl.
        apply j_cndnot. apply j_cndex. eapply (j_inselstar _ _ _ (freshlist (length tml) :: List.nil)).
        eapply (j_btbcons _ _ _ s0). rewrite length_freshlist. exact e. apply p_freshlist.
        apply j_tbquery. exact Hq'.
        apply j_btbnil. eapply (j_query_j_db _ _ _ _ Hq).
        apply tech_j_cond_fold; auto. rewrite length_freshlist. reflexivity.
        apply p_freshlist.
        apply (j_query_j_db _ _ _ _ HWF). apply incl_refl.
    - cut (j_cond d g (ttcond d (tml NOT IN q))). 
      * intro Htt. exists Htt. eexists. Unshelve. Focus 2. simpl. eapply j_cndmemb. all:eauto. split.
        ++ intro h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite IHq. simpl in Htt.
           pose (jq_q_schema _ _ _ _ Hq). generalize Htt; clear Htt. intro Htt.
           pose (s1 := freshlist (length tml)).
           assert (j_cond d (s1 :: g) (List.fold_right (fun (ta : pretm * Name) acc =>
              let (t, a) := ta in (tmvar (0,a) IS NULL) OR (((tm_lift t 1) IS NULL) OR cndeq (tm_lift t 1) (tmvar (0, a))) AND acc) (TRUE) (combine tml s1))).
           -- inversion Htt. inversion X. inversion X0. inversion X1. inversion X4. inversion X3. subst.
              unfold s1. exact X2.
           -- assert (HlenT : Rel.T (length s0) = Rel.T (list_sum (List.map (length (A:=Name)) (s1 :: Datatypes.nil)))).
              simpl. f_equal. unfold s1. rewrite plus_0_r. rewrite length_freshlist. exact e.
              erewrite (cond_sem_not_ex_selstar _ _ _ _ _ Hq' _ _ _ _ X). Unshelve.
              Focus 2. exact HlenT.
               f_equal.
              destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
                    (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e)
                    (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
                 (fun rl : Rel.T (length tml) => fold_right2
                  (fun (r0 V0 : Value) (acc : bool) => (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool)
                  true (length tml) rl (Ev.v_tml_sem g tml Html h)))) eqn:e1.
              ** transitivity false.
                 destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
                      (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e) 
                      (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
                  (fun rl : Rel.T (length tml) => fold_right2
                   (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
                   (length tml) rl (Ev.v_tml_sem g tml Html h)))); reflexivity. (* this is how to use conj1 *)
                 symmetry. transitivity (negb true); try reflexivity.
                 rewrite <- e1 at 1. f_equal. f_equal. apply eq_card_dep; auto.
                 apply eq_sel; auto.
                 +++ rewrite <- e. intros. rewrite H. reflexivity.
                 +++ intros. apply tech_sem_not_exists. unfold s1. rewrite length_freshlist. reflexivity.
                    generalize r1 r2 H; clear r1 r2 H.
                    rewrite <- e. intros. rewrite H.
                    generalize HlenT; clear HlenT.
                    simpl. unfold s1. rewrite length_freshlist. rewrite <- e. rewrite plus_0_r.
                    intro HlenT. rewrite (UIP_refl _ _ HlenT). reflexivity.
              ** transitivity true. (* this is how to use conj2 *)
                 +++ apply if_false; auto.
                     generalize e1; clear e1. apply bool_contrapos.
                     intro. apply Nat.ltb_lt in H. apply Nat.ltb_lt.
                     apply (lt_le_trans _ _ _ H). apply le_card_eq_not_neq.
                 +++ symmetry. transitivity (negb false); try reflexivity. f_equal.
                     rewrite <- e1. f_equal. apply eq_card_dep; auto.
                     apply eq_sel; auto.
                     --- rewrite <- e. intros. rewrite H. reflexivity.
                     --- intros. apply tech_sem_not_exists. unfold s1. apply length_freshlist.
                         generalize r1 r2 H; clear r1 r2 H.
                         rewrite <- e. intros. rewrite H.
                         generalize HlenT; clear HlenT.
                         simpl. unfold s1. rewrite length_freshlist. rewrite <- e. rewrite plus_0_r.
                         intro HlenT. rewrite (UIP_refl _ _ HlenT). reflexivity.
              ** unfold s1. rewrite length_freshlist. rewrite e. reflexivity.
        ++ intro h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite IHq.
           destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
            (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e) (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
            (fun rl : Rel.T (length tml) =>
              fold_right2 (fun (r0 V0 : Value) (acc : bool) => (acc && S3.is_btrue (S3.veq r0 V0))%bool) true
              (length tml) rl (Ev.v_tml_sem g tml Html h)))) eqn:e0.
           -- transitivity true. reflexivity. symmetry. apply if_true.
              ** rewrite <- e0 at 1. rewrite fold_v_tml_sem1. reflexivity.
              ** reflexivity.
           -- transitivity false.
              ** destruct (0 <? Rel.card (Rel.sel (cast (Rel.R (length s0)) (Rel.R (length tml))
                    (eq_ind_r (fun n : nat => Rel.R n = Rel.R (length tml)) eq_refl e)
                    (SQLSem2.q_sem d g (ttquery d q) s0 Hq' h))
                   (fun rl : Rel.T (length tml) => fold_right2 (fun (r0 V0 : Value) (acc : bool) => 
                    (acc && negb (S3.is_bfalse (S3.veq r0 V0)))%bool) true (length tml) rl 
                    (Ev.v_tml_sem g tml Html h))));reflexivity.
              ** symmetry. apply if_false.
                 +++ rewrite <- e0. rewrite fold_v_tml_sem1. reflexivity.
                 +++ apply if_elim; reflexivity.
      * simpl.
        apply j_cndnot. apply j_cndex. eapply j_inselstar.
        eapply (j_btbcons _ _ _ s0). rewrite length_freshlist. exact e. apply p_freshlist.
        apply j_tbquery. exact Hq'.
        apply j_btbnil. eapply (j_query_j_db _ _ _ _ Hq).
        apply tech_j_cond_fold; auto. rewrite length_freshlist. reflexivity.
        apply p_freshlist.
        apply (j_query_j_db _ _ _ _ HWF). apply incl_refl.
  + intros g q Hq IHq.
    case IHq. clear IHq. intros Hq' IHq.
    eexists. Unshelve. Focus 2. eapply j_cndex. eauto.
    eexists. Unshelve. Focus 2. eapply j_cndnot. eapply j_cndex. eauto.
    split.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
      rewrite IHq. cut (forall b, S3.is_btrue (S3.of_bool b) = S2.is_btrue (S2.of_bool b)).
      intro Hcut. apply Hcut. intro. Bool.destr_bool.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
      rewrite IHq. cut (forall b, S3.is_btrue (negtb (S3.of_bool b)) = S2.is_btrue (S2.bneg (S2.of_bool b))).
      intro Hcut. apply Hcut. intro. Bool.destr_bool.
  + intros g c1 c2 Hc1 IHc1 Hc2 IHc2.
    case IHc1. clear IHc1. intros Hc1' IHc1. case IHc1. clear IHc1. intros Hc1'' IHc1. 
    case IHc1. clear IHc1. intros IHc1' IHc1''.
    case IHc2. clear IHc2. intros Hc2' IHc2. case IHc2. clear IHc2. intros Hc2'' IHc2.
    case IHc2. clear IHc2. intros IHc2' IHc2''.
    eexists. Unshelve. Focus 2. eapply j_cndand. all:eauto.
    eexists. Unshelve. Focus 2. eapply j_cndor. all:eauto.
    split.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
      rewrite S3_is_btrue_and. rewrite S2_is_btrue_and.
      rewrite IHc1', IHc2'. reflexivity.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite negtb_andtb.
      rewrite S3_is_btrue_or. rewrite S2_is_btrue_or.
      rewrite IHc1'', IHc2''. reflexivity.
  + intros g c1 c2 Hc1 IHc1 Hc2 IHc2.
    case IHc1. clear IHc1. intros Hc1' IHc1. case IHc1. clear IHc1. intros Hc1'' IHc1. 
    case IHc1. clear IHc1. intros IHc1' IHc1''.
    case IHc2. clear IHc2. intros Hc2' IHc2. case IHc2. clear IHc2. intros Hc2'' IHc2.
    case IHc2. clear IHc2. intros IHc2' IHc2''.
    eexists. Unshelve. Focus 2. eapply j_cndor. all:eauto.
    eexists. Unshelve. Focus 2. eapply j_cndand. all:eauto.
    split.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
      rewrite S3_is_btrue_or. rewrite S2_is_btrue_or.
      rewrite IHc1', IHc2'. reflexivity.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite negtb_ortb.
      rewrite S3_is_btrue_and. rewrite S2_is_btrue_and.
      rewrite IHc1'', IHc2''. reflexivity.
  + intros g c Hc IHc.
    case IHc. clear IHc. intros Hc' IHc. case IHc. clear IHc. intros Hc'' IHc.
    case IHc. clear IHc. intros IHc' IHc''.
    eexists. Unshelve. Focus 2. exact Hc''.
    eexists. Unshelve. Focus 2. exact Hc'. split.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
      rewrite IHc''. reflexivity.
    - intro h. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite negtb_negtb.
      rewrite IHc'. reflexivity.
  (** mutual induction cases: j_btb *)
  + intros g Hdb. eexists. Unshelve. Focus 2. apply j_btbnil. assumption.
    intro h. simpl. repeat rewrite eq_rect_r_eq_refl. reflexivity.
  + intros g T s0 s1 btb g1 e Hnodup HT IHT Hbtb IHbtb.
    case IHT. clear IHT. intros HT' IHT.
    case IHbtb. clear IHbtb. intros Hbtb' IHbtb.
    eexists. Unshelve. Focus 2. eapply j_btbcons. all:eauto.
    intro h. simpl. repeat rewrite eq_rect_r_eq_refl.
    rewrite IHT, IHbtb. reflexivity.
  (** mutual induction cases: j_inquery *)
  + intros c b btm btb g g1 Hbtb IHbtb Hcond IHcond Html.
    case IHbtb. clear IHbtb. intros Hbtb' IHbtb.
    case IHcond. clear IHcond. intros Hcond' IHcond.
    case IHcond. clear IHcond. intros Hcond'' IHcond.
    case IHcond. clear IHcond. intros IHcond _. clear Hcond''.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_inselect. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    apply eq_JMeq. f_equal. f_equal.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - apply JMeq_eq. eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. reflexivity.
    - apply JMeq_eq. eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. reflexivity.
  + intros g btb g1 c b Hbtb IHbtb Hcond IHcond.
    case IHbtb. clear IHbtb. intros Hbtb' IHbtb.
    case IHcond. clear IHcond. intros Hcond' IHcond.
    case IHcond. clear IHcond. intros Hcond'' IHcond.
    case IHcond. clear IHcond. intros IHcond _. clear Hcond''.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_inselstar. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    apply eq_JMeq. f_equal. apply JMeq_eq.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. f_equal. f_equal. f_equal.
      * f_equal. f_equal. f_equal. extensionality Vl. rewrite IHcond. reflexivity.
      * f_equal. f_equal. f_equal. f_equal. extensionality Vl. rewrite IHcond. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_sum. rewrite Rel.p_sum.
      rewrite IHbtb. simpl. f_equal. f_equal. f_equal.
      * f_equal. f_equal. f_equal. extensionality Vl. rewrite IHcond. reflexivity.
      * f_equal. f_equal. f_equal. f_equal. extensionality Vl. rewrite IHcond. reflexivity.
  + intros g b q1 q2 s0 Hq1 IHq1 Hq2 IHq2.
    case IHq1. clear IHq1. intros Hq1' IHq1.
    case IHq2. clear IHq2. intros Hq2' IHq2.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_inunion. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    apply eq_JMeq. f_equal. apply JMeq_eq.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_plus. rewrite Rel.p_plus.
      rewrite IHq1, IHq2. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_plus. rewrite Rel.p_plus.
      rewrite IHq1, IHq2. reflexivity.
  + intros g b q1 q2 s0 Hq1 IHq1 Hq2 IHq2.
    case IHq1. clear IHq1. intros Hq1' IHq1.
    case IHq2. clear IHq2. intros Hq2' IHq2.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_ininters. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    apply eq_JMeq. f_equal. apply JMeq_eq.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_inter. rewrite Rel.p_inter.
      rewrite IHq1, IHq2. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite Rel.p_inter. rewrite Rel.p_inter.
      rewrite IHq1, IHq2. reflexivity.
  + intros g b q1 q2 s0 Hq1 IHq1 Hq2 IHq2.
    case IHq1. clear IHq1. intros Hq1' IHq1.
    case IHq2. clear IHq2. intros Hq2' IHq2.
    eexists. Unshelve. Focus 2.
    simpl. eapply j_inexcept. all:eauto.
    intro. simpl. repeat rewrite eq_rect_r_eq_refl.
    apply eq_JMeq. f_equal. apply JMeq_eq.
    case (sumbool_of_bool b); intro e; try rewrite e; clear e.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_minus. rewrite Rel.p_minus.
      rewrite IHq1, IHq2. reflexivity.
    - eapply (p_ext' _ _ eq_refl). intro. simpl.
      rewrite Rel.p_minus. rewrite Rel.p_minus.
      rewrite Rel.p_flat. rewrite Rel.p_flat.
      rewrite IHq1, IHq2. reflexivity.
Qed.

End Translation2V.