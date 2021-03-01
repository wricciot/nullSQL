Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Util RelFacts Common.

Module Type EV.
  Import Db.

  Parameter preenv : Type.  (* environment (for evaluation) *)
  Parameter env : Ctx -> Type.
  Parameter env_lookup  : forall G : Ctx, env G -> FullVar -> option Value.

  Hypothesis env_of_tuple : forall G, forall Vl : Db.Rel.T (list_sum (List.map (List.length (A:=Name)) G)), env G.

  Hypothesis env_app : forall G1 G2, env G1 -> env G2 -> env (G1++G2).

  Hypothesis subenv1 : forall G1 G2, env (G1++G2) -> env G1.

  Parameter tuple_of_env : forall G, env G -> Db.Rel.T (list_sum (List.map (List.length (A:=Name)) G)).

End EV.

Module Evl <: EV.
  Import Db.

  Definition preenv := list Value. (* environment (for evaluation) *)
  Definition env := fun (g : Ctx) => 
    { h : preenv & (List.length (List.concat g) =? List.length h) = true }. 

  Fixpoint scm_env s (h : preenv) {struct s} : list (Name * Value) * preenv := 
    match s, h with
    | List.nil, _ => (List.nil, h)
    | _, List.nil => (List.nil, List.nil)
    | a::s0, v::h0 => let (sh,h') := scm_env s0 h0 in ((a,v)::sh,h')
    end. 

  Fixpoint ctx_env G (h : preenv) {struct G} : list (list (Name * Value)) :=
    match G with
    | List.nil => List.nil
    | s::G0 => let (sh,h') := scm_env s h in sh :: ctx_env G0 h'
    end.

  Definition env_lookup : forall G : Ctx, env G -> FullVar -> option Value :=
    fun G h x => let (n,a) := x in
      bind (nth_error (ctx_env G (projT1 h)) n)
        (fun sh => bind (find (fun x => if Db.Name_dec (fst x) a then true else false) sh)
          (fun p => ret (snd p))).

  Lemma j_var_nth_aux (h : list Value) s a : forall i,
    findpos s (fun x => if Db.Name_dec x a then true else false) 0 = Some i ->
    length s = length h ->
    { v : Value & nth_error h i = Some v }.
  Proof.
    intros. cut (nth_error h i <> None).
    + destruct (nth_error h i); intuition. exists v; reflexivity.
    + apply nth_error_Some. rewrite <- H0. pose (findpos_Some _ _ _ _ _ H). omega.
  Qed.

  Lemma nth_error_map A B n a (f : A -> B) : 
    forall (l : list A), nth_error l n = Some a ->
    nth_error (List.map f l) n = Some (f a).
  Proof.
    elim n; simpl.
    + intro l; destruct l; simpl; intuition.
      - discriminate H.
      - injection H. intro. rewrite H0. reflexivity.
    + intros m IH l; destruct l; simpl; intuition. discriminate H.
  Qed.

  Lemma nth_error_map_r A B n b (f : A -> B) : 
    forall (l : list A), nth_error (List.map f l) n = Some b ->
    { a : A & nth_error l n = Some a /\ b = f a }.
  Proof.
    elim n; simpl.
    + intro l; destruct l; simpl; intuition.
      - discriminate H.
      - injection H. intro. exists a. rewrite H0. auto.
    + intros m IH l; destruct l; simpl; intuition. discriminate H.
  Qed.

(*
  Lemma env_scm_length (G : Ctx) (h : env G) : forall n s, 
    List.nth_error G n = Some s -> { h0 : list Value & List.nth_error (projT1 h) n = Some h0 /\ length s = length h0 }.
  Proof.
    intros. destruct h. pose (nth_error_map _ _ _ _ (@length Name) _ H).
    clearbody e0. rewrite e in e0. destruct (nth_error_map_r _ _ _ _ _ _ e0).
    destruct a. exists x0. simpl. auto.
  Qed.

  Definition unopt {A} : forall (x : option A), x <> None -> A.
    refine (fun x => match x as x0 return (x0 <> None -> A) with Some x' => fun _ => x' | None => _ end).
    intro Hfalse. contradiction Hfalse. reflexivity.
  Defined.
*)

  Lemma unopt_pi {A} (x : option A) Hx Hx' : unopt x Hx = unopt x Hx'.
  Proof.
    destruct x; intuition.
    contradiction Hx. reflexivity.
  Qed.

  Lemma p_scm_preenv s G (h : preenv) :
    length h = length (List.concat (s::G)) ->
    forall y h0, scm_env s h = (y,h0) ->
    length y = length s /\ length h0 = length h - length s.
  Proof.
    intros. generalize s, H, y, h0, H0. clear s H y h0 H0. induction h; simpl; intros.
    + destruct s.
      - simpl in H0. injection H0. intros. subst. intuition.
      - simpl in H. discriminate H.
    + destruct s.
      - simpl. simpl in H0. injection H0; intros; subst. simpl; intuition.
      - simpl in H0. destruct (scm_env s h) eqn:e0. injection H0; intros; clear H0. 
        simpl in H. injection H. intro. clear H.
        destruct (IHh _ H0 _ _ e0). subst. split.
        * simpl. rewrite H. reflexivity.
        * rewrite H3. simpl. reflexivity.
  Qed.

  Lemma p_scm_env s G (h : env (s::G)) :
    forall y p, scm_env s (projT1 h) = (y,p) ->
    length y = length s /\ length p = length (projT1 h) - length s.
  Proof.
    intros. destruct h. simpl in e. eapply (p_scm_preenv _ G). symmetry.
    apply Nat.eqb_eq. exact e. exact H.
  Qed.

  Definition env_hd {a} {s} {G} : env ((a::s)::G) -> Value.
    refine (fun h => unopt (List.hd_error (projT1 h)) _).
    destruct h. simpl. destruct x; simpl; intuition. discriminate H.
  Defined.

  Definition env_tl {a} {s} {G} : env ((a::s)::G) -> env (s::G).
    refine (fun h => _).
    enough ((length (concat (s::G)) =? length (List.tl (projT1 h))) = true).
    unfold env. econstructor. exact H.
    destruct h. destruct x; simpl; intuition.
  Defined.

  Fixpoint env_skip {s} {G} {s0} : env ((s0++s)::G) -> env (s::G).
   refine (match s0 with List.nil => _ | a0::s1 => _ end).
   + refine (fun h => h).
   + refine (fun h => env_skip _ _ _ (env_tl h)).
  Defined.

  Inductive j_var_sem : forall s, Name -> (env (s::List.nil) -> Value) -> Prop :=
  | jvs_hd : forall a s, ~ List.In a s -> j_var_sem (a::s) a (fun h => env_hd h)
  | jvs_tl : forall a s b, 
      forall Sb, a <> b -> j_var_sem s b Sb -> j_var_sem (a::s) b (fun h => Sb (env_tl h)).

  Theorem j_var_sem_fun :
    forall s a Sa, j_var_sem s a Sa -> forall Sa0, j_var_sem s a Sa0 -> Sa = Sa0.
  Proof.
    intros s a Sa Ha. induction Ha.
    + intros. inversion H0.
      - apply (existT_eq_elim H5). intros _. apply JMeq_eq.
      - contradiction H5. reflexivity.
    + intros. inversion H0.
      - contradiction H.
      - apply (existT_eq_elim H3); clear H3; intros; subst.
        rewrite (IHHa _ H6). reflexivity.
  Qed.

  Lemma j_var_sem_In : 
    forall s a Sa, j_var_sem s a Sa -> List.In a s.
  Proof.
    intros. induction H; intuition.
  Qed.

  Definition subenv1 {G1} {G2} : env (G1++G2) -> env G1.
    refine (fun h => _).
    enough ((length (concat G1) =? length (firstn (length (concat G1)) (projT1 h))) = true).
    unfold env. econstructor. exact H.
    destruct h. apply Nat.eqb_eq. symmetry. apply firstn_length_le.
    simpl. rewrite <- (proj1 (Nat.eqb_eq _ _) e). rewrite concat_app. rewrite app_length. omega.
  Defined.

  Definition subenv2 {G1} {G2} : env (G1++G2) -> env G2.
    refine (fun h => _).
    enough ((length (concat G2) =? length (skipn (length (concat G1)) (projT1 h))) = true).
    unfold env. econstructor. exact H.
    destruct h. apply Nat.eqb_eq. simpl. rewrite length_skipn.
    rewrite <- (proj1 (Nat.eqb_eq _ _) e). rewrite concat_app. rewrite app_length. omega.
  Defined.

  Definition env_app : forall G1 G2, env G1 -> env G2 -> env (G1++G2).
    refine (fun G1 G2 h1 h2 => existT _ (projT1 h1 ++ projT1 h2) _).
    destruct h1. destruct h2. apply Nat.eqb_eq. 
    rewrite concat_app. simpl. do 2 rewrite app_length. 
    f_equal; apply Nat.eqb_eq.
    exact e.
    exact e0.
  Defined.

  Fixpoint env_of_tuple G : Db.Rel.T (list_sum (List.map (List.length (A:=Name)) G)) -> env G.
    refine 
      ((match G as G0 return (G = G0 -> Db.Rel.T (list_sum (List.map (@length Name) G0)) -> env G0) with
      | List.nil => _
      | List.cons s G1 => _
      end) eq_refl).
    + refine (fun _ _ => existT _ List.nil _). reflexivity.
    + simpl. intros. pose (p := split X); clearbody p.
      apply (env_app (s :: List.nil)).
      - eapply (existT _ (Vector.to_list (fst p)) _). Unshelve. simpl.
        rewrite length_to_list. rewrite app_length. simpl. apply Nat.eqb_eq. omega.
      - apply (env_of_tuple _ (snd p)).
  Defined.

  Definition tuple_of_env G : env G -> Db.Rel.T (list_sum (List.map (List.length (A:=Name)) G)).
    refine (fun h => cast _ _ _ (of_list (projT1 h))).
    unfold Rel.T. f_equal. rewrite <- length_concat_list_sum. symmetry.
    destruct h; simpl. destruct (Nat.eqb_eq (length (concat G)) (length x)). auto.
  Defined.

  Lemma of_list_to_list_opp A n (v : Vector.t A n) :
    of_list (to_list v) ~= v.
  Proof.
    induction v; simpl; intuition.
    apply Vector_cons_equal. change (length (to_list v) ~= n). apply eq_JMeq; apply length_to_list.
    reflexivity.
    apply IHv.
  Qed.

  Lemma tl_of_list_to_list A n (v : Vector.t A (S n)) :
    tl v ~= of_list (List.tl (to_list v)).
  Proof.
    eapply (caseS (fun _ v0 => tl v0 ~= of_list (List.tl (to_list v0))) _ v). Unshelve.
    simpl; intros. change (t ~= of_list (to_list t)). rewrite of_list_to_list_opp. reflexivity.
  Qed.

  Lemma env_skip_skip s1 s2 s3 G (h1 : env (((s1 ++ s2) ++ s3)::G)) (h2 : env ((s1 ++ (s2 ++ s3))::G)) :
    h1 ~= h2 -> env_skip h1 ~= env_skip (env_skip h2).
  Proof.
    intro. induction s1.
    + rewrite H. reflexivity.
    + apply IHs1.
      eapply (f_JMequal (@env_tl a ((s1++s2)++s3) _) (@env_tl a (s1++(s2++s3)) _) h1 h2); intuition.
      rewrite app_assoc. reflexivity.
      Unshelve.
      rewrite app_assoc. reflexivity.
      rewrite app_assoc. reflexivity.
  Qed.

  Lemma env_skip_single a s G (h : env (((a::List.nil)++s)::G)) :
    env_skip h ~= env_tl h.
  Proof.
    reflexivity.
  Qed.

  Lemma hd_tuple_of_env a s G (h : env ((a::s)::G)) : 
    Vector.hd (tuple_of_env _ h) = env_hd h.
  Proof.
    change (@hd Rel.V (list_sum (List.map (List.length (A:=Name)) (s::G))) (tuple_of_env ((a::s)::G) h) = env_hd h).
    destruct h. unfold tuple_of_env. simpl. unfold env_hd.
    simpl. eapply unopt_elim. destruct x; simpl.
    + intros. discriminate H.
    + intros. injection H; intro; subst. apply JMeq_eq.
      generalize (proj1 (Nat.eqb_eq _ _) e); simpl; intro. injection H0; clear H0; intro H0.
      apply (@JMeq_trans _ _ _ _ (hd (cons _ y _ (of_list x)))).
      eapply (f_JMequal (@hd _ _) (@hd _ _ ) _ _ _ _). reflexivity.
      Unshelve.
      rewrite <- H0. rewrite <- length_concat_list_sum. rewrite app_length. reflexivity.
      rewrite <- H0. rewrite <- length_concat_list_sum. rewrite app_length. reflexivity.
      rewrite <- H0. rewrite <- length_concat_list_sum. rewrite app_length. reflexivity.
      apply cast_JMeq. reflexivity.
  Qed.

  Lemma tl_tuple_of_env a s G (h : env ((a::s)::G)) : 
    Vector.tl (tuple_of_env _ h) = tuple_of_env _ (env_tl h).
  Proof.
    destruct h. unfold tuple_of_env. simpl.
    apply JMeq_eq. symmetry. apply cast_JMeq.
    rewrite tl_of_list_to_list. apply (f_JMeq _ _ (@of_list _) _ _).
    f_equal. transitivity (to_list (of_list x)). symmetry; apply to_list_of_list_opp.
    apply to_list_eq. rewrite <- (proj1 (Nat.eqb_eq _ _) e).
    simpl. rewrite app_length. f_equal.
    change (length s + length (concat G) = length s + list_sum (List.map (@length _) G)).
    f_equal. apply length_concat_list_sum.
    symmetry. apply cast_JMeq. reflexivity.
  Qed.

  Definition Vector_combine {A} {B} {n} : Vector.t A n -> Vector.t B n -> Vector.t (A * B) n :=
    Vector.rect2 (fun n0 _ _ => Vector.t (A*B) n0) (Vector.nil _)
    (fun m _ _ acc a b => Vector.cons _ (a,b) _ acc).

  Lemma length_tolist A n (v : Vector.t A n): length (to_list v) = n.
  Proof.
    elim v; simpl; intuition.
  Qed.

  Lemma nth_error_app2_eq {A} (G2:list A) n : forall G1, nth_error (G2 ++ G1) (length G2 + n) = nth_error G1 n.
  Proof.
    elim G2; auto.
  Qed.

  Lemma scm_env_skipn s : forall l h h0, scm_env s h = (l, h0) -> h0 = skipn (length s) h.
  Proof.
    induction s.
    + simpl; intros. injection H; intuition.
    + intros. destruct h.
      - simpl in H. simpl. injection H; intuition.
      - simpl in H. simpl. destruct (scm_env s h) eqn:e. injection H. intros. 
        subst. apply (IHs _ _ _ e).
  Qed.

  Lemma skipn_skipn {A} m n : forall (l : list A), skipn m (skipn n l) = skipn (m+n) l.
  Proof.
    induction n.
    + simpl; intuition. replace (m + 0) with m. reflexivity. omega.
    + intro. destruct l.
      - simpl. destruct m; simpl; intuition.
      - replace (m + S n) with (S (m + n)). simpl. apply IHn.
        omega.
  Qed.

  Lemma skipn_append {A} (l1 l2 : list A) : skipn (length l1) (l1 ++ l2) = l2.
  Proof.
    induction l1; simpl; intuition.
  Qed.

  Lemma nth_error_ctx_env_app_eq G2 n : forall G1 h1 h2,
      length (concat G1) = length h1 ->
      length (concat G2) = length h2 ->
      nth_error (ctx_env (G2 ++ G1) (h2 ++ h1)) (length G2 + n)
      = nth_error (ctx_env G1 h1) n.
  Proof.
    induction G2; simpl; intuition.
    + replace h2 with (@List.nil Value). reflexivity.
      symmetry. apply length_zero_iff_nil. intuition.
    + destruct (scm_env a (h2++h1)) eqn:e. rewrite app_length in H0.
      enough (length (h2++h1) = length (List.concat (a::G2++G1))).
      destruct (p_scm_preenv _ _ _ H1 _ _ e).
      simpl in H1. rewrite concat_app in H1. repeat rewrite app_length in H1.
      enough (length p = length (concat G2) + length (concat G1)).
      rewrite <- (firstn_skipn (length (concat G2)) p).
      replace (skipn (length (concat G2)) p) with h1.
      apply IHG2. exact H. rewrite firstn_length. rewrite H4. rewrite min_l. reflexivity. omega.
      rewrite (scm_env_skipn _ _ _ _ e). 
      rewrite skipn_skipn. 
      replace (length (concat G2) + length a) with (length h2). symmetry. apply skipn_append.
      omega.
      rewrite H3. rewrite app_length. omega.
      simpl. rewrite concat_app. do 3 rewrite app_length. omega.
  Qed.

  Lemma length_env {G} (h: env G) : length (projT1 h) = length (concat G).
  Proof.
    destruct h. simpl. symmetry. apply Nat.eqb_eq. exact e.
  Qed.

  Definition env_of_list (G:Ctx) : forall (l: list Value), length l = length (List.concat G) -> env G.
    intros. exists l. apply Nat.eqb_eq. intuition.
  Defined.

  Lemma bool_eq_pi : forall (b1 b2 : bool) (e1 e2 : b1 = b2), e1 = e2.
  Proof.
    intros b1 b2. enough (forall (x y : bool), x = y \/ x <> y).
    destruct b1, b2. 
    + intro. eapply (K_dec H (fun e => forall e2 : true = true, e = e2) _ e1). Unshelve.
      simpl. intro. eapply (K_dec H (fun e => eq_refl = e) _ e2). Unshelve. reflexivity.
    + intros. discriminate e1.
    + intros. discriminate e1.
    + intro. eapply (K_dec H (fun e => forall e2 : false = false, e = e2) _ e1). Unshelve.
      simpl. intro. eapply (K_dec H (fun e => eq_refl = e) _ e2). Unshelve. reflexivity.
    + intros. destruct (Bool.bool_dec x y); intuition.
  Qed.

  Lemma env_eq {G} (h1 h2: env G) : projT1 h1 = projT1 h2 -> h1 = h2.
  Proof.
    destruct h1. destruct h2. simpl. intro. subst. f_equal. apply bool_eq_pi.
  Qed.

  Lemma env_JMeq {G1} {G2} (h1: env G1) (h2: env G2): G1 = G2 -> projT1 h1 = projT1 h2 -> h1 ~= h2.
  Proof.
    intro. subst.
    destruct h1. destruct h2. simpl. intro. subst. apply eq_JMeq. f_equal. apply bool_eq_pi.
  Qed.

  Inductive j_fvar_sem : forall G, nat -> Name -> (env G -> Value) -> Prop :=
  | jfs_hd : forall s G a, 
      forall Sa, j_var_sem s a Sa -> j_fvar_sem (s::G) O a (fun h => Sa (@subenv1 (s::List.nil) G h))
  | jfs_tl : forall s G i a,
      forall Sia, j_fvar_sem G i a Sia -> j_fvar_sem (s::G) (S i) a (fun h => Sia (@subenv2 (s::List.nil) G h)).

  Theorem j_fvar_sem_fun :
    forall G i a Sia, j_fvar_sem G i a Sia -> forall Sia0, j_fvar_sem G i a Sia0 -> Sia = Sia0.
  Proof.
    intros G i a Sia Hia. induction Hia.
    + intros. inversion H0. apply (existT_eq_elim H2); clear H2; intros; subst. clear H2.
      rewrite (j_var_sem_fun _ _ _ H _ H5). reflexivity.
    + intros. inversion H. apply (existT_eq_elim H5); clear H5; intros; subst.
      rewrite (IHHia _ H4). reflexivity.
  Qed.

  Lemma j_var_sem_skip s a Sa s0:
    j_var_sem s a Sa -> 
    forall Sa', j_var_sem (s0 ++ s) a Sa' ->
    forall h, Sa' h = Sa (env_skip h).
  Proof.
    intros H1. elim s0.
    + intros. simpl. replace Sa' with Sa. reflexivity.
      eapply j_var_sem_fun. exact H1. exact H.
    + simpl; intros a0 s1 IH Sa' HSa' h. inversion HSa'.
      - contradiction H3. apply in_or_app. right. apply (j_var_sem_In _ _ _ H1).
      - rewrite <- (IH _ H5). apply (existT_eq_elim H2).
        intros _ Heq. rewrite <- Heq. reflexivity.
  Qed.

  Lemma j_var_sem_not_In s0 s a Sa :
    j_var_sem (s0 ++ a :: s) a Sa -> ~ List.In a s.
  Proof.
    intro. induction s0; simpl in H.
    + inversion H; subst; intuition.
    + inversion H; subst; intuition. eapply IHs0. exact H5. exact H0.
  Qed.

  Lemma j_var_sem_inside_eq s0 s a Sa :
    j_var_sem (s0 ++ a :: s) a Sa ->
    forall h, Sa h = env_hd (env_skip h).
  Proof.
    intros H1 h. enough (~ List.In a s).
    generalize (jvs_hd a s H). intro H2.
    apply (j_var_sem_skip _ _ _ _ H2 _ H1).
    apply (j_var_sem_not_In _ _ _ _ H1).
  Qed.

  Lemma j_fvar_sem_inside_eq s0 a s G Sa : 
    j_fvar_sem ((s0 ++ a :: s)::G) 0 a Sa ->
    forall h, Sa h = env_hd (env_skip (@subenv1 ((s0 ++ a :: s)::List.nil) _ h)).
  Proof.
    intros H1 h. inversion H1; subst. apply (existT_eq_elim H0); intros; subst; clear H0 H.
    apply (j_var_sem_inside_eq _ _ _ _ H4).
  Qed.

  Lemma j_var_sem_inside s0 s a : 
    NoDup (s0 ++ a :: s) ->
    exists Sa, j_var_sem (s0 ++ a :: s) a Sa.
  Proof.
    intro. induction s0; simpl.
    + eexists. constructor. simpl in H. inversion H; subst. exact H2.
    + simpl in H. inversion H; subst. decompose record (IHs0 H3); rename x into Sa.
      eexists. constructor.
      - intro. apply H2. subst. apply in_or_app. right. constructor. reflexivity.
      - exact H0.
  Qed.

  Lemma j_fvar_sem_inside s0 a s G : 
    NoDup (s0 ++ a :: s) ->
    exists Sa, j_fvar_sem ((s0 ++ a :: s)::G) 0 a Sa.
  Proof.
    intros H1.
    decompose record (j_var_sem_inside _ _ _ H1); rename x into Sa.
    eexists; constructor; exact H.
  Qed.

End Evl.

Module Type SEM.
  Import Db.
  Parameter B : Type.
  Parameter btrue : B.
  Parameter bfalse : B.
  Parameter bmaybe : B.
  Parameter band : B -> B -> B.
  Parameter bor : B -> B -> B.
  Parameter bneg : B -> B.
  Parameter is_btrue : B -> bool.
  Parameter is_bfalse : B -> bool.
  Parameter of_bool : bool -> B.
  Parameter veq : Value -> Value -> B.

  Hypothesis sem_bpred : forall n, (forall l : list BaseConst, length l = n -> bool) -> 
    forall l : list Value, length l = n -> B.

  Hypothesis sem_bpred_elim : 
    forall n (p : forall l, length l = n -> bool) (l : list Value) (Hl : length l = n) (P : B -> Prop),
    (forall cl, monadic_map (fun val => val) l = Some cl -> forall Hcl : length cl = n, P (of_bool (p cl Hcl))) ->
    (monadic_map (fun val => val) l = None -> P bmaybe) ->
    P (sem_bpred n p l Hl).
End SEM.

Module Sem2 <: SEM.
  Import Db.
  Definition B := bool.
  Definition btrue := true.
  Definition bfalse := false.
  Definition bmaybe := false.
  Definition band := andb.
  Definition bor := orb.
  Definition bneg := negb.
  Definition is_btrue := fun (x : bool) => x.
  Definition is_bfalse := fun (x : bool) => negb x.
  Definition of_bool := fun (x : bool) => x.
  Definition veq := fun v1 v2 => 
    match v1, v2 with
    | Some x1, Some x2 => c_eq x1 x2
    | _, _ => false
    end.

  Definition sem_bpred_aux
  : forall n (p : (forall l : list BaseConst, length l = n -> bool)), 
      forall (l : list Value), length l = n -> 
      { b : B & (forall x Hx, monadic_map (fun val => val) l = Some x -> b = of_bool (p x Hx)) /\
                (monadic_map (fun val => val) l = None -> b = false)}.
  Proof.
    intros n p l H.
    destruct (monadic_map (fun val => val) l) eqn:e.
    + eexists (of_bool (p l0 _)). Unshelve. Focus 2. 
      rewrite <- (length_monadic_map _ _ _ _ _ e). exact H. split.
      - intros. injection H0. intro. generalize Hx. clear Hx. rewrite <- H1.
        intro. f_equal. f_equal. eapply UIP.
      - intro Hfalse. discriminate Hfalse.
    + exists false. split; intros.
      - discriminate H0.
      - reflexivity.
  Defined.

  Definition sem_bpred 
  : forall n, (forall l : list BaseConst, length l = n -> bool) -> 
      forall l : list Value, length l = n -> B :=
  fun n p l H => projT1 (sem_bpred_aux n p l H).

  Lemma sem_bpred_elim n (p : forall l, length l = n -> bool) (l : list Value) (Hl : length l = n) (P : B -> Prop) :
    (forall cl, monadic_map (fun val => val) l = Some cl -> forall Hcl : length cl = n, P (of_bool (p cl Hcl))) ->
    (monadic_map (fun val => val) l = None -> P false) ->
    P (sem_bpred n p l Hl).
  intros. cut ((forall x Hx, monadic_map (fun val => val) l = Some x -> sem_bpred n p l Hl = of_bool (p x Hx)) /\
                (monadic_map (fun val => val) l = None -> sem_bpred n p l Hl = false)).
  + intro Hcut. destruct Hcut. destruct (monadic_map (fun val => val) l) eqn:e; simpl.
    - assert (length l0 = n). rewrite <- Hl. symmetry. apply (length_monadic_map _ _ _ _ _ e).
      rewrite (H1 _ H3). apply H. reflexivity. reflexivity.
    - rewrite (H2 eq_refl). apply H0. reflexivity.
  + apply (projT2 (sem_bpred_aux n p l Hl)).
  Qed.

End Sem2.

Module Sem3 <: SEM.
  Import Db.
  Definition B := tribool.
  Definition btrue := ttrue.
  Definition bfalse := tfalse.
  Definition bmaybe := unknown.
  Definition band := andtb.
  Definition bor := ortb.
  Definition bneg := negtb.
  Definition is_btrue := Tribool.eqb ttrue.
  Definition is_bfalse := Tribool.eqb tfalse.
  Definition of_bool := tribool_of_bool.
  Definition veq := fun v1 v2 => 
    match v1, v2 with
    | Some x1, Some x2 => tribool_of_bool (c_eq x1 x2)
    | _, _ => unknown
    end.

  Definition sem_bpred_aux
  : forall n (p : (forall l : list BaseConst, length l = n -> bool)), 
      forall (l : list Value), length l = n -> 
      { b : B & (forall x Hx, monadic_map (fun val => val) l = Some x -> b = of_bool (p x Hx)) /\
                (monadic_map (fun val => val) l = None -> b = unknown)}.
  Proof.
    intros n p l H.
    destruct (monadic_map (fun val => val) l) eqn:e.
    + eexists (of_bool (p l0 _)). Unshelve. Focus 2. 
      rewrite <- (length_monadic_map _ _ _ _ _ e). exact H. split.
      - intros. injection H0. intro. generalize Hx. clear Hx. rewrite <- H1.
        intro. f_equal. f_equal. eapply UIP.
      - intro Hfalse. discriminate Hfalse.
    + exists unknown. split; intros.
      - discriminate H0.
      - reflexivity.
  Defined.

  Definition sem_bpred 
  : forall n, (forall l : list BaseConst, length l = n -> bool) -> 
      forall l : list Value, length l = n -> B :=
  fun n p l H => projT1 (sem_bpred_aux n p l H).

  Lemma sem_bpred_elim n (p : forall l, length l = n -> bool) (l : list Value) (Hl : length l = n) (P : B -> Prop) :
    (forall cl, monadic_map (fun val => val) l = Some cl -> forall Hcl : length cl = n, P (of_bool (p cl Hcl))) ->
    (monadic_map (fun val => val) l = None -> P unknown) ->
    P (sem_bpred n p l Hl).
  intros. cut ((forall x Hx, monadic_map (fun val => val) l = Some x -> sem_bpred n p l Hl = of_bool (p x Hx)) /\
                (monadic_map (fun val => val) l = None -> sem_bpred n p l Hl = unknown)).
  + intro Hcut. destruct Hcut. destruct (monadic_map (fun val => val) l) eqn:e; simpl.
    - assert (length l0 = n). rewrite <- Hl. symmetry. apply (length_monadic_map _ _ _ _ _ e).
      rewrite (H1 _ H3). apply H. reflexivity. reflexivity.
    - rewrite (H2 eq_refl). apply H0. reflexivity.
  + apply (projT2 (sem_bpred_aux n p l Hl)).
  Qed.

End Sem3.

