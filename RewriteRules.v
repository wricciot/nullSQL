Require Import Eqdep Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool 
  Semantics JMeq FunctionalExtensionality Omega Coq.Init.Specif Translation2V ProofIrrelevance.

Module RewriteRules (Db : DB) (Sql : SQL Db).
  Import Db.
  Import Sql.

  Module S2 := Sem2 Db.
  Module S3 := Sem3 Db.
  Module Ev := Evl Db Sql.
  Module SQLSem2 := SQLSemantics Db S2 Sql Ev.
  Module SQLSem3 := SQLSemantics Db S3 Sql Ev.

  Definition tml_of_scm s n := List.map (fun a => tmvar (n,a)) s.
  Definition btm_of_tml (tml : list pretm) (al : list Name) := List.combine tml al.
  Definition btm_of_scm s al n := btm_of_tml (tml_of_scm s n) al.

  Lemma sel_true {n} (S : Rel.R n) p : (forall r, List.In r (Rel.supp S) -> p r = true) -> Rel.sel S p = S.
  Proof.
    intro. apply Rel.p_ext. intro. destruct (p t) eqn:ept.
    + rewrite Rel.p_selt; auto.
    + rewrite Rel.p_self; auto. destruct (Rel.memb S t) eqn:eSt; auto.
      erewrite H in ept. discriminate ept.
      apply Rel.p_fs. rewrite eSt. omega.
  Qed.

(*
  Lemma cast_id A p a : cast A A p a = cast A A eq_refl a.
  Proof.
    rewrite (UIP_refl _ _ p).
*)

(*** XXX: currently in Translation2V, needs to be shared (e.g. in Facts.v) ***)
Axiom list_sum_ext: forall Hdec l1,
    forall l2, (forall x, count_occ Hdec l1 x = count_occ Hdec l2 x) ->
    list_sum l1 = list_sum l2.
Axiom eq_memb_dep : forall m n (e : m = n), forall (S1 : Rel.R m) (S2 : Rel.R n) r1 r2,
  S1 ~= S2 -> r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2.
Axiom eq_times_dep : forall m1 m2 n1 n2 (e1 : m1 = n1) (e2 : m2 = n2), 
  forall (R1 : Rel.R m1) (R2 : Rel.R m2) (S1 : Rel.R n1) (S2 : Rel.R n2),
  R1 ~= S1 -> R2 ~= S2 -> Rel.times R1 R2 ~= Rel.times S1 S2.
Axiom p_ext_dep : forall m n (e : m = n), forall (S1 : Rel.R m) (S2 : Rel.R n),
  (forall r1 r2, r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2) -> S1 ~= S2.

Axiom daemon : forall (P : Prop), P.

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

  Lemma JMeq_eq_rect_r A x (T : A -> Type) U t y e (u : U) : T y = U -> t ~= u -> @eq_rect_r _ x T t y e ~= u.
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

  Lemma f_JMeq : forall A (T : A -> Type) (f : forall a, T a) x y, x = y -> f x ~= f y.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.

  Lemma existT_projT2_eq {A} {P : A -> Type} a (p1 p2 :  P a) (e : existT _ _ p1 = existT _ _ p2)
    : p1 = p2.
  Proof.
    transitivity (projT2 (existT P a p1)). reflexivity. 
    transitivity (projT2 (existT P a p2)). apply JMeq_eq. eapply (f_JMeq _ _ (@projT2 A P) _ _ e).
    reflexivity.
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

(*
  Derive Inversion j_nil_btb_sem with (forall d G G' Snil, SQLSem3.j_btb_sem d G G' List.nil Snil) Sort Prop.

  not the inversion I'd expect, so I'll use a customized version
*)

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


  Derive Inversion j_cons_btb_sem with (forall d G G' T s tl Scons, SQLSem3.j_btb_sem d G G' ((T,s)::tl) Scons) Sort Prop.

  Lemma j_commutative_join_btb d G T1 T2 s1 s2 Ga Gb S1 S2 h :
    forall ra rb (r1 : Rel.T (length s1)) (r2 : Rel.T (length s2)), 
    ra ~= Vector.append r1 r2 -> rb ~= Vector.append r2 r1 ->
    SQLSem3.j_btb_sem d G Ga ((T1,s1)::(T2,s2)::List.nil) S1 ->
    SQLSem3.j_btb_sem d G Gb ((T2,s2)::(T1,s1)::List.nil) S2 ->
      Rel.memb (S1 h) ra = Rel.memb (S2 h) rb.
  Proof.
    intros.
    (* some case analysis (inversion) *)
    eapply (j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H1). Unshelve.
      clear H1; intros; subst. apply (existT_eq_elim H12); clear H11 H12; intros; subst. 
      apply (existT_eq_elim (JMeq_eq H4)); clear H4 H3; intros; subst.
    clear H3. eapply (j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H8). Unshelve.
      clear H8; intros; subst. apply (existT_eq_elim H15); clear H15 H14; intros; subst.
      apply (existT_eq_elim (JMeq_eq H10)); clear H7 H10; intros; subst.
    clear H7. inversion H8. eapply (j_nil_btb_sem _ _ _ _ _ _ H8). Unshelve.
      clear H8; intros. subst. clear H11 H13.
    eapply (j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H2). Unshelve.
      clear H2; intros; subst. apply (existT_eq_elim H18); clear H17 H18; intros; subst.
      apply (existT_eq_elim (JMeq_eq H12)); clear H11 H12; intros; subst.
    clear H11. eapply (j_cons_btb_sem _ _ _ _ _ _ _ (fun d0 G0 G1 T0 s0 tl0 S0 => _) _ H8). Unshelve.
      clear H8; intros; subst. apply (existT_eq_elim H20); clear H19 H20; intros; subst.
      apply (existT_eq_elim (JMeq_eq H15)); clear H14 H15; intros; subst.
    clear H14. eapply (j_nil_btb_sem _ _ _ _ _ _ H12). Unshelve.
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

  Lemma tech_commutative_join A B (l1 : list A) (l2 : list B) f g h :
    (forall x, count_occ Nat.eq_dec (List.map f l1) x = count_occ Nat.eq_dec (List.map g (List.map h l1)) x) ->
    (forall x, count_occ Nat.eq_dec (List.map g (List.map h l1)) x = count_occ Nat.eq_dec (List.map g l2) x) ->
    forall x, count_occ Nat.eq_dec (List.map f l1) x = count_occ Nat.eq_dec (List.map g l2) x.
  Proof.
    intuition. etransitivity. apply H. apply H0.
  Qed.

  Axiom tech2_commutative_join : forall A B C (l : list A) (f : A -> C) (g : B -> C) (h : A -> B),
    (forall x, f x = g (h x)) ->
    List.map f l = List.map g (List.map h l).

  Axiom tech3_commutative_join : forall A B Hdec g (h : A -> B) l1 l2,
    (forall x, count_occ Hdec (List.map h l1) x = count_occ Hdec l2 x) ->
    forall x, count_occ Nat.eq_dec (List.map g (List.map h l1)) x = count_occ Nat.eq_dec (List.map g l2) x.

  Axiom tech4_commutative_join : forall A B HdecA HdecB (h : A -> B) p1 p2 l1 l2,
    (forall x, count_occ HdecA l1 x = count_occ HdecB l2 (h x) /\ p1 x = p2 (h x)) ->
    forall x, count_occ HdecB (List.map h (List.filter p1 l1)) x = count_occ HdecB (List.filter p2 l2) x.

  (** XXX: copied from Semantics **)
  (* naturally splits a Vector of size (m+n) into two Vectors of sizes m and n *)
  Fixpoint split {A} {m} {n} : Vector.t A (m+n) -> (Vector.t A m * Vector.t A n).
  refine
  (match m as m return Vector.t A (m+n) -> (Vector.t A m * Vector.t A n) with
   | 0 => fun v => (nil _,v)
   | S p => fun v => let h := Vector.hd v in let t := Vector.tl v in
      let (v1,v2) := split _ _ _ t in
      (Vector.cons _ h _ v1,v2)
   end).
  Defined.

  Definition flip {A} {m} {n} : Vector.t A (m + n) -> Vector.t A (n + m) :=
    fun v => let (v1,v2) := split v in Vector.append v2 v1.

  Lemma eq_T_eqb_iff {m} {n} (t1 t2 : Rel.T m) (t3 t4 : Rel.T n) : 
    (t1 = t2 <-> t3 = t4) -> Rel.T_eqb t1 t2 = Rel.T_eqb t3 t4.
  Proof.
    destruct (Rel.T_eqb t1 t2) eqn:e1; destruct (Rel.T_eqb t3 t4) eqn:e2; intuition; auto.
    + rewrite <- e2. symmetry. apply Rel.T_eqb_eq. apply H0. apply Rel.T_eqb_eq. exact e1.
    + rewrite <- e1. apply Rel.T_eqb_eq. apply H1. apply Rel.T_eqb_eq. exact e2.
  Qed.

  Lemma cast_fun_app A B A' B' (ea : A = A') (eb : B = B') :
    forall (e : (A -> B) = (A' -> B')) (f : A -> B) (x : A') (y : B'), 
    (forall x', x ~= x' -> f x' ~= y)
    -> cast _ _ e f x = y.
  Proof.
    rewrite ea, eb. intro e. rewrite (UIP_refl _ _ e). intros. simpl.
    apply JMeq_eq. apply H. reflexivity.
  Qed.

  Lemma split_0_l {A} {n} (v : Vector.t A (0 + n)) :
    forall (v0 : Vector.t A n), v ~= v0 <-> split v = (Vector.nil _, v0).
  Proof.
    simpl. intuition.
    + rewrite H; reflexivity.
    + injection H; intuition; rewrite H0; reflexivity.
  Qed.

  Lemma hd_equal {A} {m} {n} (v1 : Vector.t A (S m)) (v2 : Vector.t A (S n)) :
    m = n -> v1 ~= v2 -> hd v1 = hd v2.
  Proof.
    intro. subst. intro. rewrite H. reflexivity.
  Qed.

  Lemma tl_equal {A} {m} {n} (v1 : Vector.t A (S m)) (v2 : Vector.t A (S n)) :
    m = n -> v1 ~= v2 -> tl v1 ~= tl v2.
  Proof.
    intro. subst. intro. rewrite H. reflexivity.
  Qed.

  Lemma cons_equal {A} : forall h1 h2 n1 n2 t1 t2,
    h1 = h2 -> n1 = n2 -> t1 ~= t2 -> cons A h1 n1 t1 ~= cons A h2 n2 t2.
  Proof.
    intros. generalize t1 t2 H1; clear t1 t2 H1. rewrite H, H0.
    intros. rewrite H1. reflexivity.
  Qed.

  Lemma fst_split_0_r {A} {n} (v : Vector.t A (n + 0)) : fst (split v) ~= v.
  Proof.
    generalize dependent v. induction n; simpl.
    + intro. eapply (case0 _ _ v). Unshelve. reflexivity.
    + intros. eapply (caseS' v). simpl. intros.
      replace (split t) with (fst (split t), snd (split t)). simpl.
      apply cons_equal. reflexivity. omega. apply IHn.
      rewrite surjective_pairing. reflexivity.
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

  Lemma split_0_r {A} {n} (v : Vector.t A (n + 0)) :
    forall (v0 : Vector.t A n), v ~= v0 <-> split v = (v0, Vector.nil _).
  Proof.
    induction n; simpl; intuition.
    + f_equal. eapply (case0 _ _ v0). eapply (case0 (fun v => v = nil A) _ v). Unshelve.
      reflexivity. reflexivity.
    + injection H. intuition. subst. reflexivity.
    + generalize dependent H. apply (caseS' v). apply (caseS' v0).
      intuition. simpl. destruct (IHn t0 t). rewrite H0.
      f_equal. f_equal. 
      enough (hd (cons A h0 (n+0) t0) = hd (cons A h n t)). exact H2. apply hd_equal.
      omega. exact H.
      enough (tl (cons A h0 (n+0) t0) ~= tl (cons A h n t)). exact H2. apply tl_equal.
      omega. exact H.
    + generalize dependent H. apply (caseS' v). apply (caseS' v0).
      intuition. simpl in H. replace (split t0) with (fst (split t0), snd (split t0)) in H.
      enough (fst (cons A h0 n (fst (split t0)), snd (split t0)) ~= fst (cons A h n t, nil A)).
      simpl in H0. rewrite <- H0. apply cons_equal. reflexivity. apply plus_0_r. symmetry. apply fst_split_0_r.
      rewrite H. reflexivity. rewrite surjective_pairing. reflexivity.
  Qed.

  Lemma vec_append_inj {A} {m} {n} {v1 v2 : Vector.t A m} {v3 v4 : Vector.t A n}
    : append v1 v3 = append v2 v4 -> v1 = v2 /\ v3 = v4.
  Proof.
    induction m; simpl.
    + eapply (case0 (fun v0 => append v0 v3 = append v2 v4 -> v0 = v2 /\ v3 = v4)).
      eapply (case0 (fun v0 => append (nil A) v3 = append v0 v4 -> nil A = v0 /\ v3 = v4)).
      simpl; intuition.
    + eapply (caseS' v1). eapply (caseS' v2).
      intros h2 t2 h1 t1. simpl. intro H.
      destruct (cons_inj H). destruct (IHm _ _ H1). subst. intuition.
  Qed.

  Lemma flip_inv {A} {m} {n} (v1 : Vector.t A (m + n)) (v2 : Vector.t A (n + m)) : 
    flip v1 = v2 -> v1 = flip v2.
  Proof.
    intro. rewrite <- H. clear H v2. unfold flip. apply JMeq_eq.
    eapply (split_ind v1). intros.
    eapply (split_ind (append v2 v0)). intros.
    rewrite H. destruct (vec_append_inj H0). subst. reflexivity.
  Qed.

  Lemma sum_ext m n R (f g : Rel.T m -> Rel.T n) : 
    (forall x, f x = g x) -> Rel.sum R f = Rel.sum R g.
  Proof.
    intro. apply Rel.p_ext. intro.
    do 2 rewrite Rel.p_sum. repeat f_equal. extensionality x.
    destruct (Rel.T_eqb (g x) t) eqn:e; rewrite <- H in e; exact e.
  Qed.


(*

  Lemma tml_sem_cons s G :
    forall i j j1 j2 h1 h2,
    Ev.tml_sem (s::G) (concat
     ((fix aux (l0 : list (list Name)) (i0 : nat) {struct l0} : list (list pretm) :=
         match l0 with
         | Datatypes.nil => Datatypes.nil
         | a :: tl => List.map (fun x : Name => tmvar (i0, x)) a :: aux tl (S i0)
         end) (s::G) i)) j (Ev.env_app (s::List.nil) G h1 h2) ~=
    Ev.tml_sem (s::List.nil) (concat
     ((fix aux (l0 : list (list Name)) (i0 : nat) {struct l0} : list (list pretm) :=
         match l0 with
         | Datatypes.nil => Datatypes.nil
         | a :: tl => List.map (fun x : Name => tmvar (i0, x)) a :: aux tl (S i0)
         end) (s::List.nil) i)) j1 h1 ++
    Ev.tml_sem G (concat
     ((fix aux (l0 : list (list Name)) (i0 : nat) {struct l0} : list (list pretm) :=
         match l0 with
         | Datatypes.nil => Datatypes.nil
         | a :: tl => List.map (fun x : Name => tmvar (i0, x)) a :: aux tl (S i0)
         end) G i)) j2 h2.
  Proof.
    intros. simpl. induction s; simpl; intuition.
    + admit.
    + rewrite eq_rect_r_eq_refl. apply eq_JMeq. f_equal.
      -

  Lemma tml_sem_app G1 :
    forall G2 j j1 j2 h1 h2,
    Ev.tml_sem (G1 ++ G2) (tmlist_of_ctx (G1 ++ G2)) j (Ev.env_app _ _ h1 h2) 
      ~= Ev.tml_sem G1 (tmlist_of_ctx G1) j1 h1 ++ Ev.tml_sem G2 (tmlist_of_ctx G2) j2 h2.
  Proof.
    unfold tmlist_of_ctx, mapi. generalize 0 as i.
    elim G1; simpl; intuition.
    + destruct h1; simpl in e. simpl. destruct x.
      - unfold Ev.env_app. simpl. apply Ev.tml_sem_pi.
        destruct h2. simpl. apply eq_JMeq. f_equal. apply proof_irrelevance.
      - discriminate e.
    + simpl.

 destruct h2. simpl.
        apply eq_JMeq. f_equal. generalize dependent j2. generalize dependent j. generalize dependent G2.
      elim l2; simpl; intuition.
      repeat rewrite eq_rect_r_eq_refl.
      apply eq_JMeq. f_equal.
      admit.
      apply JMeq_eq. apply H0.
    + rewrite eq_rect_r_eq_refl. destruct a; simpl; intuition.
      - destruct l1. 


  Lemma tml_sem_app l1 :
    forall l2 G1 G2 j j1 j2 h1 h2,
    length l1 = length (concat G1) ->
    Ev.tml_sem (G1 ++ G2) (l1 ++ l2) j (Ev.env_app _ _ h1 h2) 
      ~= Ev.tml_sem G1 l1 j1 h1 ++ Ev.tml_sem G2 l2 j2 h2.
  Proof.
    elim l1; simpl; intuition.
    + generalize dependent j2. generalize dependent j. generalize dependent G2.
      elim l2; simpl; intuition.
      repeat rewrite eq_rect_r_eq_refl.
      apply eq_JMeq. f_equal.
      admit.
      apply JMeq_eq. apply H0.
    + rewrite eq_rect_r_eq_refl. destruct a; simpl; intuition.
      - destruct l1. 

(* makes me wonder if it is even true 

maybe it should be

    Ev.tml_sem (G1 ++ G2) (tmlist_of_ctx (G1 ++ G2)) j (Ev.env_app _ _ h1 h2) 
      ~= Ev.tml_sem G1 (tmlist_of_ctx G1) j1 h1 ++ Ev.tml_sem G2 (tmlist_of_ctx G2) j2 h2.

but this form is unlikely to be provable directly
we will probably have to unfold the def of tmlist_of_ctx
and then generalize wrt the index used in mapi
 *)

unfold Ev.env_app. simpl. 
      destruct h2.
      

*)

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

  Lemma tml_sem_app G tml1 tml2 j h :
    forall j1 j2,
      Ev.tml_sem G (tml1++tml2) j h = Ev.tml_sem G tml1 j1 h ++ Ev.tml_sem G tml2 j2 h.
  Proof.
    induction tml1; simpl; intuition.
    + apply JMeq_eq. apply Ev.tml_sem_pi. reflexivity.
    + rewrite eq_rect_r_eq_refl. f_equal.
      - apply JMeq_eq. apply Ev.tm_sem_pi. reflexivity.
      - apply IHtml1.
  Qed.

  Lemma eq_tml_sem :
    forall G1 G2, G1 = G2 -> forall tml1 tml2, tml1 = tml2 ->
    forall j1 j2 h1 h2, h1 ~= h2 ->
    Ev.tml_sem G1 tml1 j1 h1 ~= Ev.tml_sem G2 tml2 j2 h2.
  Proof.
    intros G1 G2 eG. rewrite eG.
    intros tml1 tml2 etml. rewrite etml. intros.
    apply Ev.tml_sem_pi. exact H.
  Qed.

  Lemma to_list_append {A} {m} {n} (v1:Vector.t A m) (v2:Vector.t A n) : 
    to_list (append v1 v2) = to_list v1 ++ to_list v2.
  Proof.
    elim v1; simpl; intuition.
    unfold to_list. f_equal. exact H.
  Qed.

  Axiom tm_sem_tm_var : forall (P : Value -> Prop) G n a j h,
    (forall H, P (unopt (Ev.env_lookup G h (n,a)) H)) ->
    P (Ev.tm_sem G (tmvar (n,a)) j h).

(*
  Lemma j_tm_sem_tmvar s G1 G2 h: 
    forall a Stm Hs Has, 
    Ev.j_tm_sem (G1 ++ s :: G2) (tmvar (length G1, a)) Stm ->
    Stm h = Ev.var_sem (length G1) a (G1 ++ s :: G2) s Hs Has h.
  Proof.
    intros. inversion H. 
    pose (H4' := existT_projT2_eq _ _ _ H4); clearbody H4'; clear H4.
    rewrite <- H4'. 
    enough (s = s0). subst. f_equal. apply proof_irrelevance.
    apply JMeq_eq. generalize Has0. elim Has; intros.
    + generalize (eq_refl (a::s)). 
      dependent inversion Has1 with (fun s1 (Hinv : j_var a s1)  => s1 = a::s -> Hinv ~= j_varhd a s n).
      - intro. apply eq_JMeq. f_equal. apply proof_irrelevance.
      - contradiction n0. reflexivity.
    + generalize (eq_refl (b::s)). 
      dependent inversion Has1 with (fun s1 (Hinv : j_var a s1)  => s1 = b::s -> Hinv ~= j_varcons a b s n j).
      - contradiction n.
      - intro. apply eq_JMeq. f_equal. apply proof_irrelevance. apply JMeq_eq. apply H0.
    + clear h Stm Has H Has0 H0 H2 H4'. generalize dependent Hs0. elim G1; intros.
      - injection Hs0. intuition.
      - apply H. exact Hs0.
  Qed.

  Lemma p_unopt {A} : 
    forall (P : A -> Prop) (x : option A) Hx, 
    (forall y, x = Some y -> P y) -> P (unopt x Hx).
  Proof.
    intros. destruct x. apply H. reflexivity. contradiction Hx. reflexivity.
  Qed.
*)

  Lemma projT1_env_app G1 G2 h1 h2 : 
    projT1 (Ev.env_app G1 G2 h1 h2) = projT1 h1 ++ projT1 h2.
  Proof.
    admit.
  Admitted.

  Lemma ev_split_ind {A} {m} {n} (v : Vector.t A (m + n)) :
    forall (P : forall m n, (Vector.t A m * Vector.t A n) -> Prop),
    (forall v1 v2, v = append v1 v2 -> P m n (v1,v2)) ->
    P m n (Ev.split v).
  Proof.
    admit.
  Admitted.


  Lemma projT1_env_of_tuple G x : 
    projT1 (Ev.env_of_tuple G x) = to_list x.
  Proof.
    induction G.
    + simpl in x. eapply (case0 (fun v => List.nil = to_list v) _ x). Unshelve. reflexivity.
    + simpl. simpl in x. 
      enough (forall v1 v2, x = append v1 v2 -> 
        to_list v1 ++ projT1 (Ev.env_of_tuple G v2) = to_list x).
      erewrite <- (H (fst (Ev.split x)) (snd (Ev.split x))). reflexivity.
      apply JMeq_eq.
      apply (ev_split_ind x (fun m n p => x ~= append (fst p) (snd p))).
      intros. rewrite H0. reflexivity.
      intros. rewrite H. rewrite to_list_append. f_equal. apply IHG.
  Qed.

(*
  Lemma scm_env_combine :
    forall s G x h y p,
    Ev.scm_env s (projT1 (Ev.env_app (s :: Datatypes.nil) G (Ev.env_of_tuple (s :: Datatypes.nil) x) h)) = (y,p) ->
    y = List.combine s (to_list x).
  Proof.
    intros. simpl in x. generalize x y H. clear x y H.
    induction s.
    + simpl. intros. injection H. intuition.
    + simpl. intro. 
      destruct (@Ev.split Rel.V (@length Name s) O
                         (@tl Rel.V
                            ((fix add (n m : nat) {struct n} : nat :=
                                match n return nat with
                                | O => m
                                | S p0 => S (add p0 m)
                                end) (@length Name s) O) x)) eqn:e.
      simpl. unfold Rel.V. 
      destruct (Ev.scm_env s (((fix fold_right_fix (n : nat) (v : Vector.t Value n) (b : list Value) {struct v} : 
        list Value := match v with
                      | nil _ => b
                      | cons _ a0 n0 w => a0 :: fold_right_fix n0 w b
                      end) (length s) t Datatypes.nil ++ Datatypes.nil) ++ projT1 h)) eqn:e0.
      intros y Hinj; injection Hinj; clear Hinj; intros.
      rewrite <- H0. rewrite (Vector.eta x). simpl. f_equal. apply IHs.
      rewrite <- H, <- e0. rewrite projT1_env_app. f_equal. f_equal.
      rewrite projT1_env_of_tuple. generalize (eq_JMeq e).
      eapply (ev_split_ind (tl x) (fun m n p => p ~= (t, t0) -> (_ :Prop))).
      intros. rewrite H1. simpl. rewrite (to_list_append v1 v2).
      replace (to_list v2) with (@List.nil Value). f_equal.
      injection (JMeq_eq H2). intros. rewrite H4. reflexivity.
      eapply (case0 (fun v => List.nil = to_list v) _ v2). Unshelve. reflexivity.
  Qed.

  Lemma var_sem_env_app s G1 G2 h1 h2: 
    forall a Hs Has x z1 z2 y p, 
    Ev.scm_env s (projT1 (Ev.env_app (s :: Datatypes.nil) G2 (Ev.env_of_tuple (s :: Datatypes.nil) x) h2)) = (y,p) ->
    find (fun x0 => if Db.Name_dec (fst x0) a then true else false) y = Some (z1,z2) ->
    Ev.var_sem (length G1) a (G1 ++ s :: G2) s Hs Has 
      (Ev.env_app _ _ h1 (Ev.env_app (s::List.nil) _ (Ev.env_of_tuple _ x) h2))
    = z2.
  Proof.
    intros. unfold Ev.var_sem. apply p_unopt.
    intro. unfold Ev.env_lookup. apply bind_elim.
    + intro. rewrite proj1T_env_app. 
      replace (length G1) with (length G1 + 0). rewrite Ev.nth_error_ctx_env_app_eq.
      - unfold Ev.ctx_env. rewrite H. simpl.
        intro. injection H1. clear H1. intro.
        subst. apply bind_elim.
        * intro. rewrite H0. intro. injection H1. clear H1. intro. subst.
          unfold ret. intro. injection H1; clear H1; intro. intuition.
        * intros. discriminate H2.
      - simpl. repeat rewrite app_length. rewrite length_to_list. simpl.
        f_equal. omega. destruct h2. simpl. apply Nat.eqb_eq. exact e.
      - destruct h1. simpl. apply Nat.eqb_eq. exact e.
      - omega.
    + intros. discriminate H2.
  Qed.
*)

  Derive Inversion j_nil_sem with (forall G Snil, Ev.j_tml_sem0 G List.nil Snil) Sort Prop.
  Derive Inversion j_cons_sem with (forall G hd tl Scons, Ev.j_tml_sem0 G (hd::tl) Scons) Sort Prop.

  Lemma JMeq_cast_eq S T e x y : x ~= y -> cast S T e x = y.
  Proof.
    generalize x. rewrite e. simpl. intuition. apply JMeq_eq. exact H.
  Qed.

  Lemma eq_vector_to_list {A} {m} {n} (v1 : Vector.t A m) (v2 : Vector.t A n) :
    m = n -> to_list v1 = to_list v2 -> v1 ~= v2.
  Proof.
    intro. generalize dependent v1. rewrite H. intro.
    apply (rect2 (fun {n} w1 w2 => to_list w1 = to_list w2 -> w1 ~= w2)); intuition.
    unfold to_list in H1; simpl in H1. injection H1.
    clear H1; intros. rewrite H2.
    eapply (f_JMeq _ _ (cons A b n0)). apply JMeq_eq. apply H0. exact H1.
  Qed.

  Derive Inversion j_tmvar_sem with (forall G n a Svar, Ev.j_tm_sem0 G (tmvar (n,a)) Svar) Sort Prop.
  Derive Inversion jfv_O_sem with (forall s G a Svar, Ev.j_fvar_sem (s::G) O a Svar) Sort Prop.
  Derive Inversion jfv_S_sem with (forall s G i a Svar, Ev.j_fvar_sem (s::G) (S i) a Svar) Sort Prop.

  Axiom subenv1_app : forall G1 G2 h1 h2, Ev.subenv1 (Ev.env_app G1 G2 h1 h2) = h1.
  Axiom env_app_nil_l : forall G h1 h2, Ev.env_app List.nil G h1 h2 = h2.
  Axiom env_hd_hd : forall a s G (h : Ev.env ((a::s)::G)) x, 
    List.hd_error (projT1 h) = Some x -> Ev.env_hd h = x.
  Axiom env_tl_tl : forall a s G (h : Ev.env ((a::s)::G)),
    projT1 (Ev.env_tl h) = List.tl (projT1 h).
  Axiom tl_append : forall A m n (v1 : Vector.t A (S m)) (v2 : Vector.t A n), tl (append v1 v2) = append (tl v1) v2.

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
        apply (ev_split_ind (@tl Rel.V
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
        apply (ev_split_ind (@tl Rel.V
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

  Lemma skipn_app_l : forall A (l1 l2: list A) n, n <= length l1 -> skipn n (l1++l2) = skipn n l1 ++ l2.
  Proof.
    intros. generalize dependent n. induction l1.
    + intros. simpl in H; inversion H; auto.
    + intros. destruct n; auto. simpl. apply IHl1. simpl in H. omega.
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
               apply (ev_split_ind (cast (Vector.t Rel.V (length s1 + S (length s2))) (Rel.T (length (s1 ++ a :: s2) + 0)) e (append y x))).
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

(*
  Lemma f_JMequal_pi {A : Prop} {B : A -> Type} {A' : Prop} {B' : A' -> Type} 
    {ea : A = A'} {eb : B ~= B'} :
    forall (f : forall a, B a) (g : forall a', B' a') x y, f ~= g -> f x ~= g y.

          eapply (@JMeq_trans _ x0 x1 _ (Stml0 (Ev.env_app _ _ h1 (Ev.env_app ((s1++a::s2)::List.nil) G2 
        (Ev.env_of_tuple ((s1++a::s2)::List.nil) (cast _ _ e (Vector.append y x))) h2)))).
          ++ apply eq_JMeq. f_equal.
          ++ erewrite <- (IHs2 (s1++(a::List.nil)) _ _ (tl x) _ _ h1 h2). (* Stml0' H4' (y++[hd x])' e' *)

(* mi sa che tocca affiancare a x anche y... *)

 (* apply IHl. *) admit.
      - symmetry. apply eq_JMeq. apply Vector.eta.
  Admitted.
      
      rewrite (Vector.eta x).

      cut (forall Shd Stl, Ev.j_tm_sem (G1++s::G2) (tmvar (length G1,a)) Shd ->
        Ev.j_tml_sem (G1++s::G2) (List.map (fun x1 => tmvar (length G1,x1)) l) Stl ->
        Stml ~= fun h => Vector.cons _ (Shd h) _ (Stl h)).
      intro.

cut (Stml ~= fun h => Vector.nil _).
      - intro HS. rewrite HS. eapply (case0 (fun v => nil Rel.V ~= v) _ x). Unshelve. reflexivity.
      - apply JMeq_eq. eapply (j_nil_sem _ _ (fun tml0 Stml0 => Stml0 ~= _) _ H). Unshelve.
        intros. simpl. rewrite <- (existT_projT2_eq _ _ _ H1). reflexivity.
    +
        simple inversion H. with 
          (fun tml0 Stml0 => Stml0 ~= (fun _ : Ev.env (G1 ++ Datatypes.nil :: G2) => nil Rel.V)).

    intros x Stml e H. unfold Ev.j_tml_sem in H.
    enough (forall tml0 Stml0, 
      Ev.j_tml_sem0 (G1++s::G2) tml0 Stml0 ->
      tml0 = List.map (fun x1 => tmvar (length G1,x1)) s ->
      forall h1 h2, Stml0 (Ev.env_app _ ((s::List.nil)++G2) h1 
        (Ev.env_app _ G2 (Ev.env_of_tuple (s::List.nil) (cast _ _ e x)) h2)) ~= x).
    apply H0. exact H. reflexivity.
    intros tml0 Stml0 H'. induction H'.
    + destruct s; simpl; intros.
      - eapply (case0 (fun v => nil Rel.V ~= v) _ x).
      - discriminate H0.
    +


    induction H. with (fun G0 tml0 Stml0 => G1 ++ s :: G2 = G0 -> _).
      forall 
  Qed.


  Lemma j_tml_sem_env_app_subind s2 G1 G2 : 
    forall s1 Stml,
    Ev.j_tml_sem (G1 ++ (s1 ++ s2) :: G2) (List.map (fun x1 => tmvar (length G1, x1)) s2) Stml ->
    forall (x : Rel.T (length s2)) (y : Rel.T (length s1)) e,
    forall h1 h2, Stml (Ev.env_app _ _ h1 (Ev.env_app ((s1++s2)::List.nil) G2 
        (Ev.env_of_tuple ((s1++s2)::List.nil) (cast _ _ e (Vector.append y x))) h2)) 
        ~= x.


*)

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
          rewrite projT1_env_of_tuple. rewrite projT1_env_of_tuple. rewrite projT1_env_of_tuple.
          simpl. rewrite <- app_assoc. rewrite <- app_assoc. f_equal. f_equal.
          apply JMeq_eq. eapply (f_JMequal to_list to_list). Unshelve.
          ++ rewrite plus_0_r. reflexivity.
          ++ symmetry. apply cast_JMeq. reflexivity.
          ++ rewrite plus_0_r. reflexivity.
          ++ rewrite plus_0_r. reflexivity.
    Qed.

(*
  Lemma tml_sem_env_app_subind s G1 G2 h1 h2:
    forall s0 j (x : Rel.T (length s)) (y : Rel.T (length s0)) e,
    Ev.tml_sem (G1 ++ ((s0 ++ s) :: G2)) (List.map (fun x1 => tmvar (length G1, x1)) s) j
      (Ev.env_app _ _ h1 (Ev.env_app ((s0++s)::List.nil) G2 
        (Ev.env_of_tuple _ (cast _ _ e (Vector.append y x))) h2))
    = to_list x.
  Proof.
    elim s; simpl; intuition.
    + rewrite eq_rect_r_eq_refl. apply (Vector.case0 (fun x => List.nil = to_list x)). reflexivity.
    + rewrite eq_rect_r_eq_refl.
      replace (to_list x) with (hd x::to_list (tl x)). f_equal.
      - apply tm_sem_tm_var. intro.

(* add lemma on semantics (tm_sem) of tm_var *) admit.
      - enough (Rel.T (length s0 + 1) = Rel.T (length (s0 ++ a :: Datatypes.nil))).
        enough (Rel.T (length (s0++a::List.nil) + length l) = Rel.T (length ((s0++a::List.nil) ++ l) + 0)).
        enough (j0 : j_tml (G1 ++ ((s0 ++ a :: Datatypes.nil) ++ l) :: G2) (List.map (fun x1 : Name => tmvar (length G1, x1)) l)).
        rewrite <- (H (s0++(a::List.nil)) j0 (tl x) 
          (cast _ _ H0 (Vector.append y (Vector.cons _ (hd x) _ (Vector.nil _)))) H1).
        apply JMeq_eq. apply eq_tml_sem; auto.
        * rewrite <- app_assoc. reflexivity.
        * (* various equational lemmas on equality of env_app *) admit.
        * rewrite <- app_assoc. intro. intro. apply j. right. exact H2.
        * f_equal. rewrite <- app_assoc. repeat rewrite app_length. omega.
        * rewrite app_length. reflexivity.
      - rewrite (Vector.eta x). reflexivity.
  Admitted.


  Lemma tml_sem_env_app G :
    forall G1 G2 j x h1 h2,
    Ev.tml_sem (G1 ++ G ++ G2) (tmlist_of_ctx_i G (length G1)) j 
      (Ev.env_app G1 (G ++ G2) h1 (Ev.env_app G G2 (Ev.env_of_tuple G x) h2)) ~= to_list x.
  Proof.
    induction G; simpl; intuition.
    + rewrite eq_rect_r_eq_refl. apply (Vector.case0 (fun x => List.nil ~= to_list x)). reflexivity.
    + cut (j_tml ((G1 ++ (a::List.nil)) ++ G ++ G2)
            (List.map (fun x0 : Name => tmvar (length G1, x0)) a 
            ++ tmlist_of_ctx_i G (length (G1++(a::List.nil))))).
      - intro j0.
        cut (exists e, Ev.tml_sem _ _ j0 (Ev.env_app _ _ 
          (Ev.env_app _ _ h1 (Ev.env_of_tuple (a::List.nil) (cast _ _ e (fst (split x)))))
          (Ev.env_app _ _ (Ev.env_of_tuple G (snd (split x))) h2)) ~= to_list x).
        * intro H; destruct H. eapply (JMeq_trans _ H). Unshelve. apply eq_tml_sem.
          ++ rewrite <- app_assoc. reflexivity.
          ++ rewrite app_length. rewrite plus_comm. reflexivity.
          ++ (* eq lemmas on env_app *) admit.
        * cut (Vector.t Rel.V (length a) = Rel.T (list_sum (List.map (length (A:=Name)) (a::List.nil)))).
          ++ intro e. exists e.
            enough (j1 : j_tml ((G1 ++ a :: List.nil) ++ G ++ G2) (List.map (fun x0 => tmvar (length G1, x0)) a)).
            enough (j2 : j_tml ((G1 ++ a :: List.nil) ++ G ++ G2) (tmlist_of_ctx_i G (length (G1++a::List.nil)))).
            rewrite (tml_sem_app _ _ _ _ _ j1 j2).
            replace (to_list x) with (to_list (fst (split x)) ++ to_list (snd (split x))).
            apply eq_JMeq. f_equal.
            -- generalize (fst (split x)). intro x0.
              enough (j3 : j_tml (G1 ++ (Datatypes.nil ++ a) :: G ++ G2) (List.map (fun x1 : Name => tmvar (length G1, x1)) a)).
              enough (Rel.T (@length Rel.V Datatypes.nil + length a) = 
                Rel.T (list_sum (List.map (length (A:=Name)) ((List.nil++a)::List.nil)))).
              rewrite <- (tml_sem_env_app_subind a G1 (G++G2) 
                h1 (Ev.env_app _ _ (Ev.env_of_tuple G (snd (split x))) h2) List.nil j3 x0 (Vector.nil _) H).
              ** apply JMeq_eq. apply eq_tml_sem; auto.
                +++ rewrite <- app_assoc. reflexivity.
                +++ (* eq lemmas on env_app *) admit.
              ** simpl. f_equal. omega.
              ** intro. intro. apply j. apply List.in_or_app. left. exact H.
            -- apply JMeq_eq. apply IHG.
            -- replace x with (Vector.append (fst (split x)) (snd (split x))) at 3. 
              apply split_ind. intros. symmetry. apply to_list_append.
              apply JMeq_eq.
              apply (split_ind x (fun _ _ v => append (fst v) (snd v) ~= x)). intros.
              rewrite H. reflexivity.
            -- intro. intro. rewrite <- app_assoc. simpl. apply j. apply in_or_app. right. 
              rewrite app_length in H. simpl in H. rewrite plus_comm in H. exact H.
            -- intro. intro. rewrite <- app_assoc. simpl. apply j. apply in_or_app. left. exact H.
          ++ simpl. rewrite plus_comm. reflexivity.
      - rewrite <- app_assoc. rewrite app_length. simpl. rewrite plus_comm. exact j.
  Admitted.

  Lemma v_tml_sem_env_app G G1 j x h :
    Ev.v_tml_sem (G1 ++ G) (tmlist_of_ctx G1) j (Ev.env_app G1 G (Ev.env_of_tuple G1 x) h) ~= x.
  Proof.
    unfold Ev.v_tml_sem. apply JMeq_eq_rect.
    + unfold tmlist_of_ctx. rewrite length_concat_list_sum.
      f_equal. f_equal. unfold mapi. generalize 0. elim G1; simpl; intuition.
      f_equal. rewrite map_length. reflexivity.
      rewrite H. reflexivity.
    + apply (@JMeq_trans _ _ _ _ (of_list (to_list x))).
      - eapply (f_JMequal of_list of_list _ _ JMeq_refl). Unshelve. 
        generalize dependent j. rewrite tmlist_of_ctx_O. intro. 
        enough (h0 : Ev.env List.nil).
        replace (Ev.env_app G1 G (Ev.env_of_tuple G1 x) h)
          with (Ev.env_app _ _ h0 (Ev.env_app G1 G (Ev.env_of_tuple G1 x) h)).
        apply (tml_sem_env_app G1 List.nil G j x).
        destruct h0. unfold Ev.env_app. simpl. apply JMeq_eq.
        enough (Hx0 : x0 = @List.nil (list Rel.V)).
        eapply (f_JMequal_pi
          (existT (fun h0 : Ev.preenv => List.map (length (A:=Name)) (G1 ++ G) = List.map (length (A:=Value)) h0)
            (x0 ++ projT1 (Ev.env_of_tuple G1 x) ++ projT1 h))
          (existT (fun h0 : Ev.preenv => List.map (length (A:=Name)) (G1 ++ G) = List.map (length (A:=Value)) h0)
            (projT1 (Ev.env_of_tuple G1 x) ++ projT1 h))).
        eapply (f_JMequal
          (existT (fun h0 : Ev.preenv => List.map (length (A:=Name)) (G1 ++ G) = List.map (length (A:=Value)) h0))
          (existT (fun h0 : Ev.preenv => List.map (length (A:=Name)) (G1 ++ G) = List.map (length (A:=Value)) h0))).
        Unshelve.
        reflexivity.
        rewrite Hx0; reflexivity.
        destruct x0; auto; discriminate e.
        exists List.nil. reflexivity. 
        reflexivity.
        reflexivity.
        rewrite Hx0; reflexivity.
        rewrite Hx0; reflexivity.
        reflexivity.
        reflexivity.
      - elim x; simpl; intuition.
        change cons with VectorDef.cons.
        cut (VectorDef.cons Rel.V h0 ~= VectorDef.cons Rel.V h0). intro.
        cut (VectorDef.cons Rel.V h0 (length (to_list t)) ~= VectorDef.cons Rel.V h0 n). intro.
        eapply (f_JMequal _ _ _ _ H1). Unshelve.
        exact H.
        eapply (f_JMequal _ _ _ _ H0). Unshelve.
        apply eq_JMeq. apply length_to_list. 
        reflexivity.
        rewrite length_to_list. reflexivity.
        rewrite length_to_list. reflexivity.
        reflexivity.
        reflexivity.
  Qed.
*)

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

  Lemma sub_ext_dep_elim1 m1 m2 n1 n2 f1 f2 (R2 : Rel.R m2) (P: forall n, Rel.R n -> Prop) : 
    m1 = m2 -> n1 = n2 -> f1 ~= f2 ->
    (forall (R1 : Rel.R m1), R1 ~= R2 -> P n1 (Rel.sum R1 f1)) ->
    P n2 (Rel.sum R2 f2).
  Proof.
    intros; subst. rewrite <- H1. apply H2. reflexivity.
  Qed.

  Lemma filter_supp_elim n R r (P : list (Rel.T n) -> Prop) :
    (List.In r (Rel.supp R) -> P (r::List.nil)) ->
    (~ List.In r (Rel.supp R) -> P List.nil) ->
    P (filter (fun (x0 : Rel.T n) => Rel.T_eqb x0 r) (Rel.supp R)).
  Proof.
    admit.
  Admitted.

  Lemma filter_supp_elim' m n R r (P : list (Rel.T (m+n)) -> Prop) :
    (List.In (flip r) (Rel.supp R) -> P (flip r::List.nil)) ->
    (~ List.In (flip r) (Rel.supp R) -> P List.nil) ->
    P (filter (fun x0 => Rel.T_eqb (flip x0) r) (Rel.supp R)).
  Proof.
    admit.
  Admitted.

  Lemma j_commutative_join d G T1 T2 s1 s2 sa sb S1 S2 h :
    SQLSem3.j_q_sem d G sa (SELECT * FROM ((T1,s1)::(T2,s2)::List.nil) WHERE TRUE) S1 ->
    SQLSem3.j_q_sem d G sb
      (SELECT (btm_of_tml (tml_of_scm s1 1 ++ tml_of_scm s2 0) sb) FROM ((T2,s2)::(T1,s1)::List.nil) WHERE TRUE)
      S2 ->
    forall ra rb, ra ~= rb -> Rel.memb (S1 h) ra = Rel.memb (S2 h) rb.
  Proof.
    intros. inversion H. subst. 
    apply (existT_eq_elim H9); clear H9; intros _ H9.
    apply (existT_eq_elim (JMeq_eq H9)); clear H9; intros _ HS1.
    inversion H0. subst.
    apply (existT_eq_elim H14); clear H14; intros _ H14.
    apply (existT_eq_elim (JMeq_eq H14)); clear H14; intros _ HS2.
    subst.
    assert (e' : Rel.T (length (concat G1)) = Rel.T (length (tmlist_of_ctx G1))). admit. (* simple *)
    transitivity (Rel.memb (Rel.sum (Rel.sel (Sbtb h)
        (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
            S3.is_btrue (Sc (Ev.env_app G1 G (Ev.env_of_tuple G1 Vl) h))))
      (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G1)) =>
         Stml (Ev.env_app G1 G (Ev.env_of_tuple G1 Vl) h))) (cast _ _ e' ra)).
      apply eq_memb_dep. admit (* simple *).
      apply cast_JMeq. reflexivity.
      symmetry. apply cast_JMeq. reflexivity.
      assert (eS2 : (fun _ : Ev.env G =>
        Rel.R (length (List.map snd (btm_of_tml (tml_of_scm s1 1 ++ tml_of_scm s2 0) (List.map snd tml))))) 
        ~= (fun _ : Ev.env G => Rel.R (length (List.map snd tml)))). admit. (* simple *)
      pose (HS2' := @f_JMequal _ _ _ _ eq_refl eS2 _ _ h h HS2 JMeq_refl). clearbody HS2'. simpl in HS2'.
    assert (e'' : Rel.T (length (List.map snd tml)) 
      = Rel.T (length (List.map fst (btm_of_tml (tml_of_scm s1 1 ++ tml_of_scm s2 0) (List.map snd tml))))). admit. (* simple *)
    transitivity (Rel.memb (Rel.sum
            (Rel.sel (Sbtb0 h)
               (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G2)) =>
                S3.is_btrue (Sc0 (Ev.env_app G2 G (Ev.env_of_tuple G2 Vl) h))))
            (fun Vl : Rel.T (list_sum (List.map (length (A:=Name)) G2)) =>
             Stml1 (Ev.env_app G2 G (Ev.env_of_tuple G2 Vl) h))) (cast _ _ e'' rb)).
      Focus 2. apply eq_memb_dep. admit (* simple *).
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
      (* hopefully simple *) admit.
      intros r2 Hr2.
    apply (cast_elim (Rel.R (length s2 + length s1)) (Sbtb0 h)).
      (* hopefully simple *) admit.
      intros R2 HR2.
    transitivity (Rel.memb (Rel.sum R2 flip) r2).
      Focus 2. apply eq_memb_dep.
      (* hopefully simple *) admit.
      apply sum_ext_dep.
      (* hopefully simple *) admit.
      (* hopefully simple *) admit.
      symmetry. exact HR2.
      intros. symmetry. 
      apply (cast_elim (Ev.env (s2::s1::G) -> Rel.T (length (tml_of_scm s1 1 ++ tml_of_scm s2 0))) Stml1).
        admit. (* lemmatize *)
      intros Stml1' HStml1'.
      apply (cast_elim (Ev.j_tml_sem (s2::s1::G) (tml_of_scm s1 1 ++ tml_of_scm s2 0) Stml1') H16).
        admit. (* lemmatize *)
      intros H16' _. 
      eapply (JMeq_trans _ (j_tml_sem_flip _ _ _ _ H16' _ _ _ _)). Unshelve.
      + symmetry. apply cast_JMeq. exact Hr2.
      + do 2 rewrite Rel.p_sum.
        apply (filter_supp_elim _ (Sbtb h) r1); intro;
        apply (filter_supp_elim' _ _ R2 r2 (fun l => _ = list_sum (List.map _ l))); intro; simpl.
        - f_equal. apply (cast_elim (Rel.T (list_sum (List.map (@length _) G2))) (flip r2)).
          (* rewrite <- length_concat_list_sum. -- from H9 *) admit.
          intros fr2 Hfr2. 
          eapply (eq_trans (j_commutative_join_btb _ _ _ _ _ _ _ _ _ _ _ _ 
            fr2 (fst (split r2)) (snd (split r2)) _ _ H8 H9)). Unshelve.
          apply eq_memb_dep.
          (* from H9 *) admit. exact HR2. symmetry. exact Hfr2.
          apply (split_ind r2 (fun m n p => r1 ~= append (fst p) (snd p))). intros. simpl.
          rewrite <- H2. apply (JMeq_trans Hr1). apply (JMeq_trans H1). exact Hr2.
          rewrite <- Hfr2. unfold flip.
          apply (split_ind r2 (fun m n p => (let (v1,v2) := p in append v2 v1) ~= append (snd p) (fst p))). 
          intros. simpl. reflexivity.
        - (* contradiction H+H0 (using H8 H9) *) admit.
        - (* contradiction H+H0 (using H8 H9) *) admit.
        - reflexivity.
      + eapply (f_JMequal Stml1 Stml1'). Unshelve.
        exact HStml1'. admit. admit. admit.
      + simpl. rewrite plus_0_r. exact x.
      + exact h.
      + simpl. rewrite (Nat.add_0_r (length s1)). reflexivity.
  Admitted.

End RewriteRules.