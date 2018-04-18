Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool JMeq 
  FunctionalExtensionality ProofIrrelevance EqdepFacts Omega.

  Notation " x ~= y " := (@JMeq _ x _ y) (at level 70, no associativity).

(*  Axiom UIP : forall A (a : A) (e : a = a), e = eq_refl. *)
  Lemma eq_rect_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect x P p x eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_rect_r_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect_r P p eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
  rewrite H. reflexivity.
  Qed.

  Fixpoint cmap_length {A B : Type} (f : A -> B) l : List.length (List.map f l) = List.length l.
  refine (match l with List.nil => _ | List.cons h t => _ end).
  exact eq_refl.
  simpl. f_equal. apply cmap_length.
  Defined.

  Lemma flat_map_length {A B : Type} (f : A -> list B) (l : list A)
    : List.length (List.flat_map f l) = list_sum (List.map (fun x => List.length (f x)) l).
  elim l.
  + reflexivity.
  + intros a l0 IH. simpl. rewrite app_length.
    apply f_equal. exact IH.
  Defined.

  Lemma length_concat_list_sum (A : Type) (l : list (list A)) : 
    List.length (List.concat l) = list_sum (List.map (@List.length A) l).
    rewrite <- (map_id l) at 1. rewrite <- flat_map_concat_map.
    rewrite flat_map_length. apply f_equal. apply map_ext. auto.
  Defined.

  Definition cast (A B : Type) (e : A = B) (a : A) : B.
    rewrite <- e. exact a.
  Defined.

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

Module Type EV (Db : DB) (Sql : SQL Db).

  Import Db.
  Import Sql.

  Parameter preenv : Type.  (* environment (for evaluation) *)
  Parameter env : Ctx -> Type.
  Parameter env_lookup  : forall G : Ctx, env G -> FullVar -> option Value.

  Hypothesis var_sem : forall n a g s, List.nth_error g n = Some s -> j_var a s -> env g -> Db.Value.

  Parameter tm_sem : forall G t (HWF: j_tm G t) (h : env G), Db.Value.

  Parameter tml_sem : forall (G : Ctx) (tml : list pretm) (HWF : j_tml G tml) (h : env G), list Value.
  Hypothesis p_tml_sem : forall G tml HWF h, length (tml_sem G tml HWF h) = length tml.
  Definition v_tml_sem : forall (G : Ctx) (tml : list pretm) (HWF : j_tml G tml) (h : env G), Rel.T (length tml).
    intros. rewrite <- (p_tml_sem G tml HWF h). apply of_list.
  Defined.

  Hypothesis env_of_tuple : forall G, forall Vl : Db.Rel.T (list_sum (List.map (List.length (A:=Name)) G)), env G.

  Hypothesis length_tmlist : forall c0, length (tmlist_of_ctx c0) = length (concat c0).
  Hypothesis length_tolist : forall A n (v : Vector.t A n), length (to_list v) = n.

  Parameter Vector_combine : forall A B n, Vector.t A n -> Vector.t B n -> Vector.t (A * B) n.

  Hypothesis env_app : forall G1 G2, env G1 -> env G2 -> env (G1++G2).

  Hypothesis tm_sem_pi : 
    forall G t H h, forall H' h', h ~= h' -> tm_sem G t H h ~= tm_sem G t H' h'.

  Hypothesis tml_sem_pi : 
    forall G tml H h, forall H' h', h ~= h' -> tml_sem G tml H h ~= tml_sem G tml H' h'.

  Hypothesis v_tml_sem_pi :
    forall G tml H h, forall H' h', h ~= h' -> v_tml_sem G tml H h ~= v_tml_sem G tml H' h'.

End EV.

Fixpoint findpos {A} (l : list A) (p : A -> bool) start {struct l} : option nat := 
  match l with
  | List.nil => None
  | List.cons a l0 => if p a then Some start else findpos l0 p (S start)
  end.

Module Evl (Db : DB) (Sql : SQL Db) <: EV Db Sql.
  Import Db.
  Import Sql.

  Definition preenv := list (list Value). (* environment (for evaluation) *)
  Definition env := fun g => { h : preenv & List.map (List.length (A:=Name)) g = List.map (List.length (A:=Value)) h }.
  Definition env_lookup : forall G : Ctx, env G -> FullVar -> option Value :=
    fun G h x => let (n,a) := x in
      bind (nth_error G n)
        (fun s => bind (findpos s (fun x => if Db.Name_dec x a then true else false) 0)
          (fun i => bind (nth_error (projT1 h) n)
            (fun h0 => nth_error h0 i))).

  Lemma findpos_Some A (s : list A) p :
    forall m n, findpos s p m = Some n -> n < m + length s.
  Proof.
    elim s; simpl; intros; intuition.
    + discriminate H.
    + destruct (p a); intuition.
      - injection H0. omega. 
      - pose (H _ _ H0). omega.
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

  Lemma j_var_nth_aux (h : list Value) s a : forall i,
    findpos s (fun x => if Db.Name_dec x a then true else false) 0 = Some i ->
    length s = length h ->
    { v : Value & nth_error h i = Some v }.
  Proof.
    intros. cut (nth_error h i <> None).
    + destruct (nth_error h i); intuition. exists v; reflexivity.
    + apply nth_error_Some. rewrite <- H0. pose (findpos_Some _ _ _ _ _ H). omega.
  Qed.

  Lemma j_var_nth (h : list Value) s a :
    j_var a s -> length s = length h ->
    { i : nat & { v : Value & findpos s (fun x => if Db.Name_dec x a then true else false) 0 = Some i /\ nth_error h i = Some v } }.
  Proof.
    intros. destruct (j_var_findpos _ _ X 0). destruct a0.
    destruct (j_var_nth_aux _ _ _ _ H1 H).
    exists x. exists x0. split; auto.
  Qed.

  (*
  Definition env_shadow (h : Env) (Al : list FullName) : Env.
    refine (List.filter (fun (p : FullName * Db.Value) => 
      let (A,_) := p in (negb (set_mem _ A Al))) h).
    exact FullName_dec.
  Defined.

  (* this corresponds to the last definition at the end of p.4, but uses a list of pairs h2 rather than a pair
     of lists Al, rl *)
  Definition env_update (h1 h2 : Env) :=
    let Al := List.map fst h2 in
    (env_shadow h1 Al) ++ h2.
   *)

  (* XXX: do we really need to use an explicit shadowing?
          can't we work with implicit shadowing, where the last added binding is the only one that counts? *)

(*
    match t with
    | tmconst c           => Some (Db.c_sem c)
    | tmnull              => None
    | tmvar V             => env_lookup h V
    end.
*)

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

  (*
  Definition Relation (n : nat) := Vector.t (option Value) n -> nat.

  (* cartesian product of two (bag) relations *)
  Definition Rel_times {m} (R : Relation m) {n} (S : Relation n) : Relation (m+n) :=
    fun r => let (r1,r2) := split r in R r1 * S r2.

  (* sums a Vector of nats *)
  Definition vec_sum {k} (nl : Vector.t nat k) :=
    Vector.fold_right plus nl 0.

  (* generalized cartesian product of m relations, each taken with its arity n *)
  Definition Rel_prod {m} (Rl : Vector.t { n : nat & Relation n } m) 
    : Relation (vec_sum (Vector.map (projT1 (P := fun n => Relation n)) Rl)).
    refine (Vector.t_rect _ 
      (fun k vl => Relation (vec_sum (Vector.map (projT1 (P := fun n => Relation n)) vl))) 
      _ _ _ Rl).
    + refine (fun _ => 1). (* vacuous *)
    + intro h0. elim h0. intros x R p t0 rec.
      refine (Rel_times R rec).
  Defined.

  *)

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

  Lemma unopt_pi {A} (x : option A) Hx Hx' : unopt x Hx = unopt x Hx'.
  Proof.
    destruct x; intuition.
    contradiction Hx. reflexivity.
  Qed.

  Definition var_sem : forall n a g s, List.nth_error g n = Some s -> j_var a s -> env g -> Db.Value.
    refine (fun n a G s Hg Hs h => unopt (env_lookup G h (n,a)) _).
    simpl. rewrite Hg. simpl.
    destruct (env_scm_length _ h _ _ Hg). destruct a0.
    destruct (j_var_nth _ _ _ Hs H0). destruct s0. destruct a0.
    rewrite H1. simpl. rewrite H. simpl. rewrite H2.
    intro Hfalse. discriminate Hfalse.
  Defined.

  Theorem var_sem_pi n a G s HG Hs h : 
    forall HG' Hs' h', h ~= h' -> var_sem n a G s HG Hs h ~= var_sem n a G s HG' Hs' h'.
  Proof.
    intros. unfold var_sem. apply eq_JMeq. rewrite <- H. apply unopt_pi. 
  Qed.

  Fixpoint tm_sem G t (HWF: j_tm G t) (h : env G) {struct HWF} : Db.Value :=
    match HWF with
    | j_const _ c => Db.c_sem c
    | j_null _ => Db.null
    | j_tmvar _ n a s Hg Ha => var_sem n a _ s Hg Ha h
    end.

  Fixpoint tml_sem (G : Ctx) (tml : list pretm) (HWF : j_tml G tml) (h : env G) {struct tml} : list Value.
    refine (
      (match tml as tml0 return (tml = tml0 -> list Value) with
      | List.nil => _
      | tm::tml0 => _ 
      end) eq_refl).
    all: intro; subst.
    + exact List.nil.
    + eapply List.cons.
      - eapply (tm_sem G tm _ h). Unshelve. apply HWF. simpl. auto.
      - eapply (tml_sem G tml0 _ h). Unshelve. unfold j_tml. intros. apply HWF. simpl. auto.
  Defined.

  Lemma p_tml_sem (G : Ctx) (tml : list pretm) (HWF : j_tml G tml) (h : env G) :
    length (tml_sem G tml HWF h) = length tml.
  generalize HWF. clear HWF. elim tml. auto.
  intros hd tl IH HWF. simpl. f_equal. apply IH.
  Qed.

  Definition env_app : forall G1 G2, env G1 -> env G2 -> env (G1++G2).
    refine (fun G1 G2 h1 h2 => existT _ (projT1 h1 ++ projT1 h2) _).
    destruct h1. destruct h2. do 2 rewrite map_app. rewrite e, e0. reflexivity.
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
      - eapply (existT _ (Vector.to_list (fst p)::List.nil) _). Unshelve. simpl.
        rewrite length_to_list. reflexivity.
      - apply (env_of_tuple _ (snd p)).
  Defined.

  Definition Vector_combine {A} {B} {n} : Vector.t A n -> Vector.t B n -> Vector.t (A * B) n :=
    Vector.rect2 (fun n0 _ _ => Vector.t (A*B) n0) (Vector.nil _)
    (fun m _ _ acc a b => Vector.cons _ (a,b) _ acc).

  Lemma length_tmlist c0 : length (tmlist_of_ctx c0) = length (concat c0).
  Proof.
    unfold tmlist_of_ctx. unfold mapi. generalize 0.
    elim c0; intuition. 
    simpl. do 2 rewrite app_length. rewrite cmap_length.
    f_equal. apply H.
  Qed.

  Lemma length_tolist A n (v : Vector.t A n): length (to_list v) = n.
  Proof.
    elim v; simpl; intuition.
  Qed.

  Theorem tm_sem_pi G t H h : 
    forall H' h', h ~= h' -> tm_sem G t H h ~= tm_sem G t H' h'.
  Proof.
    elim H; simpl; intros.
    + dependent inversion H'. reflexivity.
    + dependent inversion H'. reflexivity.
    + dependent inversion H'. simpl. rewrite <- H0.
      generalize e0 j0. replace s0 with s.
      - intros. apply var_sem_pi. reflexivity.
      - rewrite e in e0. injection e0. auto.
  Qed.

  Theorem tml_sem_pi : 
    forall G tml H h, forall H' h', h ~= h' -> tml_sem G tml H h ~= tml_sem G tml H' h'.
  Proof.
    intros G tml. elim tml; simpl; intros; repeat rewrite eq_rect_r_eq_refl; intuition.
    apply eq_JMeq. f_equal.
    + apply JMeq_eq. apply tm_sem_pi. exact H1.
    + apply JMeq_eq. apply H. exact H1.
  Qed.

  Definition v_tml_sem : forall (G : Ctx) (tml : list pretm) (HWF : j_tml G tml) (h : env G), Rel.T (length tml).
    intros. rewrite <- (p_tml_sem G tml HWF h). apply of_list.
  Defined.

  Lemma v_tml_sem_pi :
    forall G tml H h, forall H' h', h ~= h' -> v_tml_sem G tml H h ~= v_tml_sem G tml H' h'.
  Proof.
    intros. unfold v_tml_sem. rewrite <- (p_tml_sem G tml H h). rewrite <- (p_tml_sem G tml H' h').
    repeat rewrite eq_rect_eq_refl. rewrite (tml_sem_pi _ _ _ _ H' h' H0).
    reflexivity.
  Qed.

  Lemma nth_error_app2_eq {A} (G2:list A) n : forall G1, nth_error (G2 ++ G1) (length G2 + n) = nth_error G1 n.
  Proof.
    elim G2; auto.
  Qed.

  Lemma length_env {G} (h: env G) : length (projT1 h) = length G.
  Proof.
    generalize (projT2 h); simpl. 
    generalize (projT1 h); clear h. elim G.
    + intro p. destruct p; simpl; intuition. discriminate H.
    + intros x G' IH. destruct p; simpl; intuition.
      - discriminate H.
      - f_equal. apply IH. injection H. intros. exact H0.
  Qed.

  Lemma tm_sem_weak G1 t H1 h1:
    forall G2 H2 h2,
    tm_sem G1 t H1 h1 = tm_sem (G2 ++ G1) (tm_lift t (length G2)) H2 (env_app _ _ h2 h1).
  Proof.
    elim H1; simpl.
    + intros. dependent inversion H2. reflexivity.
    + intros. dependent inversion H2. reflexivity.
    + intros. dependent inversion H2. simpl.
      unfold var_sem. unfold env_lookup.
      cut (forall Hb1 Hb2, unopt (bind (nth_error G1 n) (fun s1 : Scm =>
        bind (findpos s1 (fun x : Name => if Db.Name_dec x a then true else false) 0)
        (fun i : nat => bind (nth_error (projT1 h1) n) (fun h0 : list Value => nth_error h0 i)))) Hb1
        = unopt (bind (nth_error (G2 ++ G1) (length G2 + n)) (fun s1 : Scm =>
          bind (findpos s1 (fun x : Name => if Db.Name_dec x a then true else false) 0)
          (fun i : nat => bind (nth_error (projT1 (env_app G2 G1 h2 h1)) (length G2 + n)) 
            (fun h0 : list Value => nth_error h0 i)))) Hb2).
      intro Hcut. apply Hcut.
      rewrite e, e0. simpl. cut (s0 = s). intro Hs0. rewrite Hs0.
      destruct (j_var_findpos a s j 0). destruct a1. rewrite H4. simpl.
      destruct (env_scm_length _ h1 _ _ e). destruct a1. rewrite H5. simpl.
      replace (nth_error (projT1 h2 ++ projT1 h1) (length G2 + n)) with (Some x0); simpl.
      intros. apply unopt_pi.
      rewrite <- H5. symmetry. replace (length G2) with (length (projT1 h2)).
      apply nth_error_app2_eq. apply length_env.
      rewrite nth_error_app2_eq in e0. rewrite e0 in e. injection e. auto.
  Qed.

End Evl.

Module Type SEM (Db : DB).
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

Module Sem2 (Db : DB) <: SEM Db.
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

  (*
  Definition sem_bpred 
  : forall n, (forall l : list BaseConst, length l = n -> bool) -> 
      forall l : list Value, length l = n -> B.
  Proof.
    intros n p l H. destruct (monadic_map (fun val => val) l) eqn:e.
    + apply (p l0). rewrite <- (length_monadic_map _ _ _ _ _ e). exact H.
    + exact false.
  Defined.

  Lemma sem_bpred_elim n (p : forall l, length l = n -> bool) (l : list Value) (Hl : length l = n) (P : B -> Prop) :
    (forall cl, monadic_map (fun val => val) l = Some cl -> forall Hcl : length cl = n, P (of_bool (p cl Hcl))) ->
    (monadic_map (fun val => val) l = None -> P unknown) ->
    P (sem_bpred n p l Hl).
  intros. destruct (monadic_map (fun val => val) l) eqn:e; simpl.
  unfold sem_bpred. rewrite e.
  *)
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

Module Sem3 (Db : DB) <: SEM Db.
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

  (*
  Definition sem_bpred 
  : forall n, (forall l : list BaseConst, length l = n -> bool) -> 
      forall l : list Value, length l = n -> B.
  Proof.
    intros n p l H.
    destruct (monadic_map (fun val => val) l) eqn:e.
    + eapply (of_bool (p l0 _)). Unshelve. rewrite <- (length_monadic_map _ _ _ _ _ e). exact H.
    + exact unknown.
  Defined.

  Lemma sem_bpred_elim n (p : forall l, length l = n -> bool) (l : list Value) (Hl : length l = n) (P : B -> Prop) :
    (forall cl, monadic_map (fun val => val) l = Some cl -> forall Hcl : length cl = n, P (of_bool (p cl Hcl))) ->
    (monadic_map (fun val => val) l = None -> P unknown) ->
    P (sem_bpred n p l Hl).
  intros. destruct (monadic_map (fun val => val) l) eqn:e; simpl.
  unfold sem_bpred. rewrite e.
  *)
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

Module SQLSemantics (Db : DB) (Sem: SEM Db) (Sql : SQL Db) (Ev : EV Db Sql).
  Import Db.
  Import Sem.
  Import Sql.
  Import Ev.

  Fixpoint q_sem d G Q s (HWF: j_query d G Q s) (h : env G) {struct HWF}
    : Db.Rel.R (List.length s)
  with tb_sem d G (x : bool) T s (HWF : j_tb d G T s) (h : env G) {struct HWF}
    : Db.Rel.R (List.length s)
  with cond_sem d G c (HWF : j_cond d G c) (h : env G) {struct HWF}
    : B
  with btb_sem d G btb G1 (HWF : j_btb d G btb G1) (h : env G) {struct HWF}
    : Db.Rel.R (List.length (List.concat G1))
  with inner_q_sem d G Q (HWF: j_inquery d G Q) (h : env G) {struct HWF}
    : { n : nat & Db.Rel.R n }.
  * refine ((match HWF in (j_query _ G0 Q0 s0) return (G = G0 -> Q = Q0 -> s = s0 -> Db.Rel.R (List.length s)) with
        | j_select _ _ _ _ _ _ _ _ _ _ _ _ => fun eqG eqQ eqS => _
        | j_selstar _ _ _ _ _ _ _ _ _ _ _ => fun eqG eqQ eqS => _
        | j_union _ _ _ _ _ _ _ _ => fun eqG eqQ eqS => _
        | j_inters _ _ _ _ _ _ _ _ => fun eqG eqQ eqS => _
        | j_except _ _ _ _ _ _ _ _ => fun eqG eqQ eqS => _
        end)
      eq_refl eq_refl eq_refl).
    all: subst.
    + refine (let S1 := btb_sem _ _ _ _ j h in
        let p := fun _ => true in
        let S2 := Db.Rel.sel S1 p in _).
      refine (let f := fun (Vl : Db.Rel.T (list_sum (List.map (length (A:=Name)) c0))) =>
        v_tml_sem _ _ j1 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h) in _).
      case (sumbool_of_bool b); intro.
      - (* DISTINCT *)
        eapply Db.Rel.flat. eapply (Db.Rel.sum S2).
        rewrite cmap_length. rewrite cmap_length in f. rewrite <- length_concat_list_sum in f. exact f.
      - eapply (Db.Rel.sum S2). rewrite cmap_length. rewrite cmap_length in f. rewrite length_concat_list_sum. exact f.
    + refine (let S1 := btb_sem _ _ _ _ j h in
        let p := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) => 
          Sem.is_btrue (cond_sem _ _ _ j0 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h))
        in
        let S2 := Db.Rel.sel S1 (cast _ _ _ p) in _).
      refine (let f := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) =>
        v_tml_sem _ _ j1 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h) in _).
      case (sumbool_of_bool b); intro.
      - (* DISTINCT *)
        eapply Db.Rel.flat. eapply (Db.Rel.sum S2). eapply (cast _ _ _ f).
        Unshelve.
        ** rewrite length_concat_list_sum. reflexivity.
        ** rewrite <- length_concat_list_sum. rewrite Ev.length_tmlist. reflexivity.
      - eapply (Db.Rel.sum S2). eapply (cast _ _ _ f). Unshelve. 
        rewrite <- length_concat_list_sum. rewrite Ev.length_tmlist. reflexivity.
    + case (sumbool_of_bool b); intro.
      - apply (Db.Rel.plus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.flat (Db.Rel.plus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    + case (sumbool_of_bool b); intro.
      - apply (Db.Rel.inter (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.flat (Db.Rel.inter (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    + case (sumbool_of_bool b); intro.
      - apply (Db.Rel.minus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.minus (Db.Rel.flat (q_sem _ _ _ _ j h)) (q_sem _ _ _ _ j0 h)).
  * refine ((match HWF in (j_tb _ G0 T0 s0) return (G = G0 -> T = T0 -> s = s0 -> Db.Rel.R (List.length s)) with
        | j_tbbase _ _ _ _ _ _  => fun eqG eqT eqS => _
        | j_tbquery _ _ _ _ _ => fun eqG eqT eqS => _
        end)
      eq_refl eq_refl eq_refl).
    all: subst.
    + apply (Db.db_rel e).
    + apply (q_sem _ _ _ _ j h).
  * refine ((match HWF in (j_cond _ G0 c0) return (G = G0 -> c = c0 -> B) with
        | j_cndtrue _ _ _ => fun eqG eqc => _
        | j_cndfalse _ _ _ => fun eqG eqc => _
        | j_cndnull _ _ _ _ _ _ => fun eqG eqc => _
        | j_cndpred _ _ _ _ _ _ _ _ => fun eqG eqC => _
        | j_cndmemb _ _ _ _ _ _ _ _ _ => fun eqG eqc => _
        | j_cndex _ _ _ _ => fun eqG eqc => _
        | j_cndand _ _ _ _ _ _ => fun eqG eqc => _
        | j_cndor _ _ _ _ _ _ => fun eqG eqc => _
        | j_cndnot _ _ _ _ => fun eqG eqc => _
        end)
      eq_refl eq_refl).
    all: subst.
    + exact btrue.
    + exact bfalse.
    + refine (of_bool (match (tm_sem _ _ j0 h) with None => b | _ => negb b end)).
    + apply (Sem.sem_bpred _ b (tml_sem _ _ j0 h)). apply Ev.p_tml_sem.
    + refine (let S := cast _ _ _ (q_sem _ _ _ _ j0 h) in
              let Vl := v_tml_sem _ _ j h in
              let Stt := Rel.sel S (fun rl => Vector.fold_right2 (fun r0 V0 acc => acc && is_btrue (veq r0 V0))%bool true _ rl Vl) in
              let Suu := Rel.sel S (fun rl => Vector.fold_right2 (fun r0 V0 acc => acc && negb (is_bfalse (veq r0 V0)))%bool true _ rl Vl) in
              let ntt := Rel.card Stt in
              let nuu := Rel.card Suu in
              if (0 <? ntt) then of_bool b
              else if (0 <? nuu) then bmaybe
              else of_bool (negb b)).
      rewrite e. reflexivity.
    + refine (of_bool (0 <? Rel.card (projT2 (inner_q_sem _ _ _ j h)))).
    + apply (band (cond_sem _ _ _ j h) (cond_sem _ _ _ j0 h)).
    + apply (bor (cond_sem _ _ _ j h) (cond_sem _ _ _ j0 h)).
    + apply (bneg (cond_sem _ _ _ j h)).
  * refine ((match HWF in (j_btb _ G' btb0 G1')
        return (G = G' -> btb = btb0 -> G1 = G1' -> Db.Rel.R (length (concat G1'))) with
        | j_btbnil _ _ _ => fun eqG eqc eqG1 => _
        | j_btbcons  _ _ _ _ _ _ _ _ _ _ _ => fun eqG eqc eqG1 => _
        end)
      eq_refl eq_refl eq_refl).
    all: subst.
    + apply Db.Rel.Rone.
    + rewrite concat_cons. rewrite app_length. rewrite <- e.
      apply (Db.Rel.times (tb_sem _ _ false _ _ j h) (btb_sem _ _ _ _ j0 h)).
  * refine ((match HWF in (j_inquery _ G0 Q0) return (G = G0 -> Q = Q0 -> { n : nat & Db.Rel.R n}) with
        | j_inselect _ _ _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_inselstar _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_inunion _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_ininters _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_inexcept _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        end)
      eq_refl eq_refl).
    all: subst.
    + refine (let S1 := btb_sem _ _ _ _ j h in
        let p := fun _ => true in
        let S2 := Db.Rel.sel S1 p in _).
      refine (let f := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) =>
        v_tml_sem _ _ j1 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h) in _).
      exists (List.length (List.map fst l)).
      case (sumbool_of_bool b); intro.
      - (* DISTINCT *)
        eapply Db.Rel.flat. eapply (Db.Rel.sum S2).
        eapply (cast _ _ _ f). Unshelve. rewrite length_concat_list_sum. reflexivity.
      - eapply (Db.Rel.sum S2). eapply (cast _ _ _ f). Unshelve. rewrite length_concat_list_sum. reflexivity.
    + refine (let S1 := btb_sem _ _ _ _ j h in
        let p := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) => 
          Sem.is_btrue (cond_sem _ _ _ j0 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h))
        in
        let S2 := Db.Rel.sel S1 (cast _ _ _ p) in _). Unshelve. Focus 2.
      apply (@eq_rect _ _ (fun x => (Rel.T x -> bool) = (Rel.T (length (concat c0)) -> bool)) eq_refl _ (length_concat_list_sum _ c0)).
      refine (let f := fun (_ : Db.Rel.T (list_sum (List.map (@length Name) c0))) =>
        Vector.nil Rel.V in _).
      exists 0.
      case (sumbool_of_bool b); intro.
      - (* DISTINCT *)
        eapply Db.Rel.flat. eapply (Db.Rel.sum S2). intro. apply f.
        rewrite <- length_concat_list_sum. apply X.
      - eapply (Db.Rel.sum S2). intro. apply f. rewrite <- length_concat_list_sum. apply X.
    + exists (List.length s). case (sumbool_of_bool b); intro.
      - apply (Db.Rel.plus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.flat (Db.Rel.plus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    + exists (List.length s). case (sumbool_of_bool b); intro.
      - apply (Db.Rel.inter (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.flat (Db.Rel.inter (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    + exists (List.length s). case (sumbool_of_bool b); intro.
      - apply (Db.Rel.minus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.minus (Db.Rel.flat (q_sem _ _ _ _ j h)) (q_sem _ _ _ _ j0 h)).
  Defined.

  Lemma eq_rect_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect x P p x eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_rect_r_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect_r P p eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
  rewrite H. reflexivity.
  Qed.

  Theorem sem_pi : forall d,
    (forall c p s j h s' j' h', h ~= h' -> s = s' /\ q_sem d c p s j h ~= q_sem d c p s' j' h') /\
    (forall c p s j h x s' j' h', h ~= h' -> s = s' /\ tb_sem d c x p s j h ~= tb_sem d c x p s' j' h') /\
    (forall c p (j j' : j_cond d c p) h h', h ~= h' -> cond_sem d c p j h ~= cond_sem d c p j' h') /\
    (forall c l c0 j h c0' j' h', h ~= h' -> c0 = c0' /\ btb_sem d c l c0 j h ~= btb_sem d c l c0' j' h') /\
    (forall c p (j j' : j_inquery d c p) h h', h ~= h' -> inner_q_sem d c p j h ~= inner_q_sem d c p j' h').
  intro. apply j_ind_mut.
  (* all: intros; inversion j'; simpl; repeat rewrite eq_rect_r_eq_refl. *)
  + intros s c x btm btb G G' Hbtb IHbtb Hc IHc Html e h s' j'. rewrite e.
    dependent inversion j' with 
      (fun G0 Q0 s0 Hinv => forall h', h ~= h' -> List.map snd btm = s0 /\
        q_sem d G (select x btm btb c) (List.map snd btm) (j_select d (List.map snd btm) c x btm btb G G' Hbtb Hc Html eq_refl) h
        ~= q_sem d G0 Q0 s0 Hinv h').
    intros. split. auto. rewrite e0. destruct (IHbtb _ _ j _ H5).
    generalize j, j0, j1, H7. clear j j0 j1 H7. rewrite <- H6.
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. repeat rewrite H7.
    destruct (sumbool_of_bool x).
    - apply eq_JMeq. f_equal. f_equal. f_equal. f_equal. f_equal. extensionality Vl.
      apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H5. reflexivity.
    - apply eq_JMeq. f_equal. f_equal. f_equal. f_equal. extensionality Vl.
      apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H5. reflexivity.
  + intros G btb G' c s x Hbtb IHbtb Hc IHc e Html h s' j'. rewrite e.
    dependent inversion j' with 
      (fun G0 Q0 s0 Hinv => forall h', h ~= h' -> concat G' = s0 /\
        q_sem d G (selstar x btb c) (concat G') (j_selstar d G btb G' c (concat G') x Hbtb Hc eq_refl Html) h
        ~= q_sem d G0 Q0 s0 Hinv h').
    intros. destruct (IHbtb _ _ j _ H4). split. rewrite e0, H5. reflexivity.
    generalize j, j0, e0, j1, H6. clear j j0 e0 j1 H6. rewrite <- H5.
    intros. rewrite e0. simpl. repeat rewrite eq_rect_r_eq_refl. repeat rewrite H6.
    destruct (sumbool_of_bool x).
    - apply eq_JMeq. f_equal. f_equal. f_equal. f_equal. extensionality Vl.
      f_equal. apply JMeq_eq. apply IHc. rewrite H4. reflexivity.
      f_equal. extensionality Vl.
      apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H4. reflexivity.
    - apply eq_JMeq. f_equal. f_equal. f_equal. extensionality Vl.
      f_equal. apply JMeq_eq. apply IHc. rewrite H4. reflexivity.
      f_equal. extensionality Vl.
      apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H4. reflexivity.
  + intros G x Q1 Q2 s HQ1 IHQ1 HQ2 IHQ2 h s' HQ1'.
    dependent inversion HQ1' with 
      (fun G0 Q0 s0 Hinv => forall h', h ~= h' -> s = s0 /\
        q_sem d G (qunion x Q1 Q2) s (j_union d G x Q1 Q2 s HQ1 HQ2) h
        ~= q_sem d G0 Q0 s0 Hinv h').
    intros. destruct (IHQ1 _ _ j _ H4). destruct (IHQ2 _ _ j0 _ H4). 
    split. auto. simpl. repeat rewrite eq_rect_r_eq_refl. 
    generalize j, j0, H6, H8. clear j j0 H6 H8. rewrite <- H5.
    intros. rewrite H6, H8. reflexivity.
  + intros G x Q1 Q2 s HQ1 IHQ1 HQ2 IHQ2 h s' HQ1'.
    dependent inversion HQ1' with 
      (fun G0 Q0 s0 Hinv => forall h', h ~= h' -> s = s0 /\
        q_sem d G (qinters x Q1 Q2) s (j_inters d G x Q1 Q2 s HQ1 HQ2) h
        ~= q_sem d G0 Q0 s0 Hinv h').
    intros. destruct (IHQ1 _ _ j _ H4). destruct (IHQ2 _ _ j0 _ H4). 
    split. auto. simpl. repeat rewrite eq_rect_r_eq_refl. 
    generalize j, j0, H6, H8. clear j j0 H6 H8. rewrite <- H5.
    intros. rewrite H6, H8. reflexivity.
  + intros G x Q1 Q2 s HQ1 IHQ1 HQ2 IHQ2 h s' HQ1'.
    dependent inversion HQ1' with 
      (fun G0 Q0 s0 Hinv => forall h', h ~= h' -> s = s0 /\
        q_sem d G (qexcept x Q1 Q2) s (j_except d G x Q1 Q2 s HQ1 HQ2) h
        ~= q_sem d G0 Q0 s0 Hinv h').
    intros. destruct (IHQ1 _ _ j _ H4). destruct (IHQ2 _ _ j0 _ H4). 
    split. auto. simpl. repeat rewrite eq_rect_r_eq_refl. 
    generalize j, j0, H6, H8. clear j j0 H6 H8. rewrite <- H5.
    intros. rewrite H6, H8. reflexivity.
  + intros x s G Hdb e h b s' HT'.
    dependent inversion HT' with
      (fun G0 T0 s0 Hinv => forall h', h ~= h' -> s = s0 /\
       tb_sem d G b (tbbase x) s (j_tbbase d x s G Hdb e) h
        ~= tb_sem d G0 b T0 s0 Hinv h').
    intros. cut (s = s'). 
    - intro. split. auto. generalize e0. clear e0. rewrite <- H3. intro.
      simpl. repeat rewrite eq_rect_r_eq_refl. apply eq_JMeq. f_equal. apply proof_irrelevance.
    - rewrite e in e0. injection e0. auto.
  + intros G Q s HQ IHQ h x s' HQ'.
    dependent inversion HQ' with
      (fun G0 Q0 s0 Hinv => forall h', h ~= h' -> s = s0 /\
        tb_sem d G x (tbquery Q) s (j_tbquery d G Q s HQ) h ~= tb_sem d G0 x Q0 s0 Hinv h').
    intros. destruct (IHQ _ _ j _ H2). split. auto.
    simpl. repeat rewrite eq_rect_r_eq_refl. apply H4.
  + intros G Hd Hc h.
    dependent inversion Hc with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G cndtrue (j_cndtrue d G Hd) h ~= cond_sem d G0 c0 Hinv h').
    intros. reflexivity.
  + intros G Hd Hc h.
    dependent inversion Hc with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G cndfalse (j_cndfalse d G Hd) h ~= cond_sem d G0 c0 Hinv h').
    intros. reflexivity.
  + intros G t b Hd Ht Hc h.
    dependent inversion Hc with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G (cndnull b t) (j_cndnull d G t b Hd Ht) h ~= cond_sem d G0 c0 Hinv h').
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. apply eq_JMeq.
    rewrite (Ev.tm_sem_pi G t Ht _ j0 _ H0). reflexivity.
  + intros G n p tv Hdb Html Hlen Hc' h.
    dependent inversion Hc' with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G (cndpred n p tv) (j_cndpred d G n p tv Hdb Html Hlen) h ~= cond_sem d G0 c0 Hinv h').
    assert (p = p1). specialize (eq_sigT_snd H2). rewrite (UIP_refl _ _ (eq_sigT_fst H2)). simpl. auto.
    rewrite H0. rewrite (UIP _ _ _ Hlen e).
    generalize p1. rewrite <- e. intro.
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite H4.
    apply eq_JMeq. apply Sem.sem_bpred_elim.
    - apply Sem.sem_bpred_elim.
      * intros. rewrite (Ev.tml_sem_pi _ _ Html _ j0 _ JMeq_refl) in H6. rewrite H5 in H6.
        injection H6. intro H7. generalize Hcl. rewrite H7. intro.
        rewrite (UIP _ _ _ Hcl0 Hcl1). reflexivity.
      * intros. rewrite (Ev.tml_sem_pi _ _ Html _ j0 _ JMeq_refl) in H6. rewrite H5 in H6. discriminate H6.
    - apply Sem.sem_bpred_elim.
      * intros. rewrite (Ev.tml_sem_pi _ _ Html _ j0 _ JMeq_refl) in H6. rewrite H5 in H6. discriminate H6.
      * intros. reflexivity.
  + intros G Q s tml b Html Hq IHq e Hc' h.
    dependent inversion Hc' with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G (cndmemb b tml Q) (j_cndmemb d G Q s tml b Html Hq e) h ~= cond_sem d G0 c0 Hinv h').
    intros. pose (jq_q_schema _ _ _ _ Hq). pose (jq_q_schema _ _ _ _ j0). clearbody e1 e2.
    rewrite e1 in e2. injection e2. intro e3. generalize j0 e0; clear j0 e0. rewrite <- e3. intros.
    rewrite <- H0. rewrite (UIP _ _ _ e0 e). simpl. repeat rewrite eq_rect_r_eq_refl.
    destruct (IHq h _ j0 _ JMeq_refl). clear IHq.
    rewrite H5. rewrite (Ev.v_tml_sem_pi _ _ Html _ j _ JMeq_refl). reflexivity.
  + intros G Q HQ IHQ Hc' h.
    dependent inversion Hc' with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G (EXISTS Q) (j_cndex d G Q HQ) h ~= cond_sem d G0 c0 Hinv h').
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. rewrite (IHQ j _ _ H0). reflexivity.
  + intros G c1 c2 Hc1 IHc1 Hc2 IHc2 Hc' h.
    dependent inversion Hc' with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G (c1 AND c2) (j_cndand d G c1 c2 Hc1 Hc2) h ~= cond_sem d G0 c0 Hinv h').
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. 
    rewrite (IHc1 j _ _ H0). rewrite (IHc2 j0 _ _ H0). reflexivity.
  + intros G c1 c2 Hc1 IHc1 Hc2 IHc2 Hc' h.
    dependent inversion Hc' with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G (c1 OR c2) (j_cndor d G c1 c2 Hc1 Hc2) h ~= cond_sem d G0 c0 Hinv h').
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. 
    rewrite (IHc1 j _ _ H0). rewrite (IHc2 j0 _ _ H0). reflexivity.
  + intros G c1 Hc1 IHc1 Hc' h.
    dependent inversion Hc' with (fun G0 c0 Hinv => forall h', h ~= h' -> 
      cond_sem d G (NOT c1) (j_cndnot d G c1 Hc1) h ~= cond_sem d G0 c0 Hinv h').
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. 
    rewrite (IHc1 j _ _ H0). reflexivity.
  + intros G Hd h G' Hbtb'.
    dependent inversion Hbtb' with (fun G0 btb0 G0' Hinv => forall h', h ~= h' -> Datatypes.nil = G0' /\
      btb_sem d G Datatypes.nil Datatypes.nil (j_btbnil d G Hd) h ~= btb_sem d G0 btb0 G0' Hinv h').
    intros. split;reflexivity.
  + intros G T s s' btb G' Hlen Hnodup HT IHT Hbtb IHbtb h G'' H'.
    dependent inversion H' with (fun G0 btb0 G0' Hinv => forall h', h ~= h' -> s' :: G' = G0' /\
      btb_sem d G ((T,s') :: btb) (s' :: G') (j_btbcons d G T s s' btb G' Hlen Hnodup HT Hbtb) h ~= btb_sem d G0 btb0 G0' Hinv h').
    intros. destruct (IHT _ false _ j _ H4). destruct (IHbtb _ _ j0 _ H4).
    generalize HT, Hbtb, H6, H8. clear HT IHT Hbtb IHbtb H6 H8.
    rewrite H4, H7. intros. simpl. split. reflexivity.
    repeat rewrite eq_rect_r_eq_refl.
    generalize H6, H8; clear H6 H8.
    generalize (btb_sem d G btb g1 Hbtb h'), (btb_sem d G btb g1 j0 h').
    generalize (tb_sem d G false T s HT h'), (tb_sem d G false T s0 j h').
    generalize Hlen; clear Hlen. rewrite H5. intros Hlen r1 r2 r3 r4 H6 H8.
    rewrite H6, H8. rewrite (UIP _ _ _ Hlen e). reflexivity.
  + intros c x btm btb G G' Hbtb IHbtb Hc IHc Html j' h.
    dependent inversion j' with 
      (fun G0 Q0 Hinv => forall h', h ~= h' ->
        inner_q_sem d G (select x btm btb c) (j_inselect d c x btm btb G G' Hbtb Hc Html) h ~=
          inner_q_sem d G0 Q0 Hinv h').
    intros. destruct (IHbtb _ _ j _ H0).
    generalize j, j0, j1, H6. clear j j0 j1 H6. rewrite <- H5.
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. repeat rewrite H6.
    apply eq_JMeq. f_equal.
    destruct (sumbool_of_bool x).
    - f_equal. f_equal. f_equal. extensionality Vl.
      apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H0. reflexivity.
    - f_equal. f_equal. extensionality Vl.
      apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H0. reflexivity.
  + intros G btb G' c x Hbtb IHbtb Hc IHc j' h .
    dependent inversion j' with 
      (fun G0 Q0 Hinv => forall h', h ~= h' ->
        inner_q_sem d G (selstar x btb c) (j_inselstar d G btb G' c x Hbtb Hc) h ~=
          inner_q_sem d G0 Q0 Hinv h').
    intros. destruct (IHbtb _ _ j _ H0).
    generalize j, j0, H5. clear j j0 H5. rewrite <- H4.
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. repeat rewrite H5. rewrite H0. apply eq_JMeq.
    f_equal. destruct (sumbool_of_bool x).
    - f_equal. f_equal. f_equal. f_equal. extensionality Vl. f_equal.
      apply JMeq_eq. apply IHc. reflexivity.
    - f_equal. f_equal. f_equal. extensionality Vl. f_equal.
      apply JMeq_eq. apply IHc. reflexivity.
  + intros G x Q1 Q2 s HQ1 IHQ1 HQ2 IHQ2 j' h.
    dependent inversion j' with 
      (fun G0 Q0 Hinv => forall h', h ~= h' ->
        inner_q_sem d G (qunion x Q1 Q2) (j_inunion d G x Q1 Q2 s HQ1 HQ2) h ~=
          inner_q_sem d G0 Q0 Hinv h').
    intros. destruct (IHQ1 _ _ j _ H0). destruct (IHQ2 _ _ j0 _ H0).
    simpl. repeat rewrite eq_rect_r_eq_refl.
    generalize j, j0, H5, H7. clear j j0 H5 H7. rewrite <- H4.
    intros. rewrite H5, H7. reflexivity.
  + intros G x Q1 Q2 s HQ1 IHQ1 HQ2 IHQ2 j' h.
    dependent inversion j' with 
      (fun G0 Q0 Hinv => forall h', h ~= h' ->
        inner_q_sem d G (qinters x Q1 Q2) (j_ininters d G x Q1 Q2 s HQ1 HQ2) h ~=
          inner_q_sem d G0 Q0 Hinv h').
    intros. destruct (IHQ1 _ _ j _ H0). destruct (IHQ2 _ _ j0 _ H0).
    simpl. repeat rewrite eq_rect_r_eq_refl.
    generalize j, j0, H5, H7. clear j j0 H5 H7. rewrite <- H4.
    intros. rewrite H5, H7. reflexivity.
  + intros G x Q1 Q2 s HQ1 IHQ1 HQ2 IHQ2 j' h.
    dependent inversion j' with 
      (fun G0 Q0 Hinv => forall h', h ~= h' ->
        inner_q_sem d G (qexcept x Q1 Q2) (j_inexcept d G x Q1 Q2 s HQ1 HQ2) h ~=
          inner_q_sem d G0 Q0 Hinv h').
    intros. destruct (IHQ1 _ _ j _ H0). destruct (IHQ2 _ _ j0 _ H0).
    simpl. repeat rewrite eq_rect_r_eq_refl.
    generalize j, j0, H5, H7. clear j j0 H5 H7. rewrite <- H4.
    intros. rewrite H5, H7. reflexivity.
Qed.

Corollary q_sem_pi :
  forall d c p s j h s' j' h', h ~= h' -> s = s' /\ q_sem d c p s j h ~= q_sem d c p s' j' h'.
Proof.
  intro d. decompose [and] (sem_pi d). assumption.
Qed.

Corollary tb_sem_pi :
  forall d c p s j h x s' j' h', h ~= h' -> s = s' /\ tb_sem d c x p s j h ~= tb_sem d c x p s' j' h'.
Proof.
  intro d. decompose [and] (sem_pi d). assumption.
Qed.

Corollary cond_sem_pi :
    forall d c p (j j' : j_cond d c p) h h', h ~= h' -> cond_sem d c p j h ~= cond_sem d c p j' h'.
Proof.
  intro d. decompose [and] (sem_pi d). assumption.
Qed.

Corollary btb_sem_pi :
  forall d c l c0 j h c0' j' h', h ~= h' -> c0 = c0' /\ btb_sem d c l c0 j h ~= btb_sem d c l c0' j' h'.
Proof.
  intro d. decompose [and] (sem_pi d). assumption.
Qed.

Corollary inner_q_sem_pi :
  forall d c p (j j' : j_inquery d c p) h h', h ~= h' -> inner_q_sem d c p j h ~= inner_q_sem d c p j' h'.
Proof.
  intro d. decompose [and] (sem_pi d). assumption.
Qed.

End SQLSemantics.