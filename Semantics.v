Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega.

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

Module Type EV (Db : DB) (Sql : SQL Db).

  Import Db.
  Import Sql.

  Parameter preenv : Type.  (* environment (for evaluation) *)
  Parameter env : Ctx -> Type.
  Parameter env_lookup  : forall G : Ctx, env G -> FullVar -> option Value.

(*
  Hypothesis var_sem : forall n a g s, List.nth_error g n = Some s -> j_var a s -> env g -> Db.Value.
*)
  Parameter j_tm_sem : forall G, pretm -> (env G -> Value) -> Prop.
  Parameter j_tml_sem : forall G (tml : list pretm), (env G -> Rel.T (List.length tml)) -> Prop.

  Hypothesis j_tm_sem_fun :
    forall G t St, j_tm_sem G t St -> forall St0, j_tm_sem G t St0 -> St = St0.
  Hypothesis j_tml_sem_fun :
    forall G tml Stml, j_tml_sem G tml Stml -> forall Stml0, j_tml_sem G tml Stml0 -> Stml = Stml0.

(*
  Parameter tm_sem : forall G t (HWF: j_tm G t) (h : env G), Db.Value.

  Parameter tml_sem : forall (G : Ctx) (tml : list pretm) (HWF : j_tml G tml) (h : env G), list Value.
  Hypothesis p_tml_sem : forall G tml HWF h, length (tml_sem G tml HWF h) = length tml.
  Definition v_tml_sem : forall (G : Ctx) (tml : list pretm) (HWF : j_tml G tml) (h : env G), Rel.T (length tml).
    intros. rewrite <- (p_tml_sem G tml HWF h). apply of_list.
  Defined.
*)

  Hypothesis env_of_tuple : forall G, forall Vl : Db.Rel.T (list_sum (List.map (List.length (A:=Name)) G)), env G.

  Hypothesis length_tmlist : forall c0, length (tmlist_of_ctx c0) = length (concat c0).
  Hypothesis length_tolist : forall A n (v : Vector.t A n), length (to_list v) = n.

  Parameter Vector_combine : forall A B n, Vector.t A n -> Vector.t B n -> Vector.t (A * B) n.

  Hypothesis env_app : forall G1 G2, env G1 -> env G2 -> env (G1++G2).

(*
  Hypothesis tm_sem_pi : 
    forall G t H h, forall H' h', h ~= h' -> tm_sem G t H h ~= tm_sem G t H' h'.

  Hypothesis tml_sem_pi : 
    forall G tml H h, forall H' h', h ~= h' -> tml_sem G tml H h ~= tml_sem G tml H' h'.

  Hypothesis v_tml_sem_pi :
    forall G tml H h, forall H' h', h ~= h' -> v_tml_sem G tml H h ~= v_tml_sem G tml H' h'.
*)
End EV.

Fixpoint findpos {A} (l : list A) (p : A -> bool) start {struct l} : option nat := 
  match l with
  | List.nil => None
  | List.cons a l0 => if p a then Some start else findpos l0 p (S start)
  end.

Module Evl (Db : DB) (Sql : SQL Db) <: EV Db Sql.
  Import Db.
  Import Sql.

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

  Lemma findpos_Some A (s : list A) p :
    forall m n, findpos s p m = Some n -> n < m + length s.
  Proof.
    elim s; simpl; intros; intuition.
    + discriminate H.
    + destruct (p a); intuition.
      - injection H0. omega. 
      - pose (H _ _ H0). omega.
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

  Lemma j_var_nth_aux (h : list Value) s a : forall i,
    findpos s (fun x => if Db.Name_dec x a then true else false) 0 = Some i ->
    length s = length h ->
    { v : Value & nth_error h i = Some v }.
  Proof.
    intros. cut (nth_error h i <> None).
    + destruct (nth_error h i); intuition. exists v; reflexivity.
    + apply nth_error_Some. rewrite <- H0. pose (findpos_Some _ _ _ _ _ H). omega.
  Qed.

(*
  Lemma j_var_nth (h : list Value) s a :
    j_var a s -> length s = length h ->
    { i : nat & { v : Value & findpos s (fun x => if Db.Name_dec x a then true else false) 0 = Some i /\ nth_error h i = Some v } }.
  Proof.
    intros. destruct (j_var_findpos _ _ X 0). destruct a0.
    destruct (j_var_nth_aux _ _ _ _ H1 H).
    exists x. exists x0. split; auto.
  Qed.
*)

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

(*
  Lemma env_scm_length (G : Ctx) (h : env G) : forall n s, 
    List.nth_error G n = Some s -> { h0 : list Value & List.nth_error (projT1 h) n = Some h0 /\ length s = length h0 }.
  Proof.
    intros. destruct h. pose (nth_error_map _ _ _ _ (@length Name) _ H).
    clearbody e0. rewrite e in e0. destruct (nth_error_map_r _ _ _ _ _ _ e0).
    destruct a. exists x0. simpl. auto.
  Qed.
*)

  Definition unopt {A} : forall (x : option A), x <> None -> A.
    refine (fun x => match x as x0 return (x0 <> None -> A) with Some x' => fun _ => x' | None => _ end).
    intro Hfalse. contradiction Hfalse. reflexivity.
  Defined.

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

(*
  Lemma scm_env_tech a s G (h : env (s::G)) :
    forall y p, 
    scm_env s (projT1 h) = (y,p) -> j_var a s ->
    find (fun x => if Db.Name_dec (fst x) a then true else false) y <> None.
  Proof.
    intros. destruct (p_scm_env _ _ _ _ _ H). destruct h. simpl in H, H1.
    generalize x, e, y, p, H, H0, H1. clear x e y p H H0 H1. induction X; simpl; intros.
    + destruct x.
      - injection H. intros. subst. discriminate H0.
      - destruct (scm_env s x). injection H. intros. subst.
        simpl. destruct (Db.Name_dec a a); simpl; intuition. discriminate H2.
    + destruct x.
      - injection H. intros. subst. discriminate H0.
      - destruct (scm_env s x) eqn:e0. injection H. intros. subst.
        simpl. destruct (Db.Name_dec b a); simpl; intuition.
        simpl in H0. injection H0; intro. 
        clear H. simpl in H1.
        assert ((length (concat (s::G)) =? length x) = true). exact e.
        apply (IHX _ H _ _ e0 H3 H1). exact H2.
  Qed.
  Lemma ctx_env_tech a s G : 
    forall n y p, length p = length (List.concat G) ->
    nth_error G n = Some s -> j_var a s -> nth_error (ctx_env G p) n = Some y ->
    find (fun x => if Db.Name_dec (fst x) a then true else false) y <> None.
  Proof.
    intros.
    generalize n, y, p, H, H0, X, H1. clear n y p H H0 X H1. induction G; intros.
    + destruct n; discriminate H0.
    + simpl in H, H0. destruct (scm_env a0 p) eqn:e.
      destruct (p_scm_preenv _ G _ H _ _ e).
      destruct n.
      - simpl in H, H0, H1. injection H0. rewrite e in H1. injection H1. intros. subst.
        eapply (scm_env_tech a s G (existT _ p _) _ _ e X).
      - simpl in H1. rewrite e in H1. eapply (IHG n y p0 _ H0 X H1). Unshelve.
        * simpl. apply Nat.eqb_eq. symmetry. exact H.
        * rewrite H3. rewrite H. rewrite app_length. omega.
  Qed.

  Definition var_sem : forall n a g s, List.nth_error g n = Some s -> j_var a s -> env g -> Db.Value.
    refine (fun n a G s Hg Hs h => unopt (env_lookup G h (n,a)) _).
    generalize dependent h. generalize dependent Hs. generalize dependent Hg.
    generalize dependent n. induction G.
    + intro. destruct n; simpl; discriminate.
    + intro. destruct n; intros.
      - injection Hg. intro. clear Hg. simpl. eapply bind_elim; intros.
        * eapply bind_elim; intros.
          ++ intro. discriminate H2.
          ++ destruct (scm_env a0 (projT1 h)) eqn:e. simpl in e. rewrite e in H0.
            injection H0. intro. subst.
            destruct (scm_env_tech _ _ _ _ _ _ e Hs H1).
        * destruct (scm_env a0 (projT1 h)) eqn:e. simpl in e. rewrite e in H0.
          discriminate H0.
      - simpl. unfold env_lookup in IHG. destruct h eqn:e0. simpl. destruct (scm_env a0 x) eqn:e1.
        eapply (IHG n Hg Hs (existT (fun h => (length (concat G) =? length h) = true) p _)). Unshelve. simpl.
        assert (length x = length (concat (a0::G))). symmetry. apply Nat.eqb_eq. exact e.
        destruct (p_scm_preenv _ _ _ H _ _ e1). rewrite H1.
        apply Nat.eqb_eq. rewrite H. 
        simpl. rewrite app_length. omega.
  Defined.

  Theorem var_sem_pi n a G s HG Hs h : 
    forall HG' Hs' h', h ~= h' -> var_sem n a G s HG Hs h ~= var_sem n a G s HG' Hs' h'.
  Proof.
    intros. unfold var_sem. apply eq_JMeq. rewrite <- H. apply unopt_pi. 
  Qed.
*)

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

(* change everything to Prop...

  Theorem j_var_sem_to_j_var s a S (Ha : j_var_sem s a S) : j_var a s.
  Proof.
    
*)

  Definition subenv1 {G1} {G2} : env (G1++G2) -> env G1.
    refine (fun h => _).
    enough ((length (concat G1) =? length (firstn (length (concat G1)) (projT1 h))) = true).
    unfold env. econstructor. exact H.
    destruct h. apply Nat.eqb_eq. symmetry. apply firstn_length_le.
    simpl. rewrite <- (proj1 (Nat.eqb_eq _ _) e). rewrite concat_app. rewrite app_length. omega.
  Defined.

  Lemma length_skipn {A} (l : list A) :
    forall n, length (skipn n l) = length l - n.
  Proof.
    induction l; simpl; intuition; case n; intuition.
  Qed.

  Definition subenv2 {G1} {G2} : env (G1++G2) -> env G2.
    refine (fun h => _).
    enough ((length (concat G2) =? length (skipn (length (concat G1)) (projT1 h))) = true).
    unfold env. econstructor. exact H.
    destruct h. apply Nat.eqb_eq. simpl. rewrite length_skipn.
    rewrite <- (proj1 (Nat.eqb_eq _ _) e). rewrite concat_app. rewrite app_length. omega.
  Defined.

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

(*
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
*)
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

(*
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
*)
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

(*
  Lemma nth_error_ctx_env {G} : 
    forall ..., nth_error G n = Some x ->
    nth_error (ctx_env G h) n = Some y.
  Proof.
    induction G; simpl; intuition.
    destruct (scm_env a h); simpl. intuition.
  Qed.
*)

(*
  Lemma tm_sem_weak G1 t H1 h1:
    forall G2 H2 h2,
    tm_sem G1 t H1 h1 = tm_sem (G2 ++ G1) (tm_lift t (length G2)) H2 (env_app _ _ h2 h1).
  Proof.
    elim H1; simpl.
    + intros. dependent inversion H2. reflexivity.
    + intros. dependent inversion H2. reflexivity.
    + intros. dependent inversion H2. simpl.
      unfold var_sem. unfold env_lookup.
      cut (forall Hb1 Hb2, unopt (bind (nth_error (ctx_env G1 (projT1 h1)) n) 
        (fun sh =>
         bind (find (fun x => if Db.Name_dec (fst x) a then true else false) sh)
         (fun p => ret (snd p)))) Hb1
        = unopt (bind (nth_error (ctx_env (G2 ++ G1) (projT1 (env_app G2 G1 h2 h1))) (length G2 + n)) 
         (fun sh =>
          bind (find (fun x => if Db.Name_dec (fst x) a then true else false) sh)
          (fun p => ret (snd p)))) Hb2).
      intro Hcut. apply Hcut. unfold env_app. simpl.
      rewrite nth_error_ctx_env_app_eq. apply unopt_pi.
      destruct h1. simpl. apply Nat.eqb_eq. exact e1.
      destruct h2. simpl. apply Nat.eqb_eq. exact e1.
  Qed.
*)

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

  Inductive j_q_sem (d : Db.D) : forall G (s : Scm), prequery -> (env G -> Rel.R (List.length s)) -> Prop := 
  | jqs_sel : forall G b tml btb c,
      forall G0 Sbtb Sc Stml e,
      j_btb_sem d G G0 btb Sbtb ->
      j_cond_sem d (G0++G) c Sc ->
      j_tml_sem (G0++G) (List.map fst tml) Stml ->
      j_q_sem d G (List.map snd tml) (select b tml btb c) 
        (fun h => let S1 := Sbtb h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Ev.env_app _ _ (Ev.env_of_tuple G0 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml (Ev.env_app _ _ (Ev.env_of_tuple G0 Vl) h) in
                  let S := cast _ _ e (Rel.sum S2 f)
                  in if b then Rel.flat S else S)
  | jqs_selstar : forall G b btb c,
      forall G0 Sbtb Sc Stml e,
      j_btb_sem d G G0 btb Sbtb ->
      j_cond_sem d (G0++G) c Sc ->
      j_tml_sem (G0++G) (tmlist_of_ctx G0) Stml ->
      j_q_sem d G (List.concat G0) (selstar b btb c) 
        (fun h => let S1 := Sbtb h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Ev.env_app _ _ (Ev.env_of_tuple G0 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml (Ev.env_app _ _ (Ev.env_of_tuple G0 Vl) h) in
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
  with j_in_q_sem (d : Db.D) : forall G, prequery -> (env G -> bool) -> Prop :=
  | jiqs_sel : forall G b tml btb c,
      forall G0 Sbtb Sc Stml,
      j_btb_sem d G G0 btb Sbtb ->
      j_cond_sem d (G0++G) c Sc ->
      j_tml_sem (G0++G) (List.map fst tml) Stml ->
      j_in_q_sem d G (select b tml btb c) 
        (fun h => let S1 := Sbtb h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Ev.env_app _ _ (Ev.env_of_tuple G0 Vl) h)) in
                  let S2 := Rel.sel S1 p in
                  let f  := fun Vl => Stml (Ev.env_app _ _ (Ev.env_of_tuple G0 Vl) h) in
                  let S := Rel.sum S2 f
                  in 0 <? Rel.card (if b then Rel.flat S else S))
  | jiqs_selstar : forall G b btb c,
      forall G0 Sbtb Sc,
      j_btb_sem d G G0 btb Sbtb ->
      j_cond_sem d (G0++G) c Sc ->
      j_in_q_sem d G (selstar b btb c) 
        (fun h => let S1 := Sbtb h in
                  let p  := fun Vl => Sem.is_btrue (Sc (Ev.env_app _ _ (Ev.env_of_tuple G0 Vl) h)) in
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
  with jiqs_ind_mut := Induction for j_in_q_sem Sort Prop.

  Combined Scheme j_sem_ind_mut from jqs_ind_mut, jTs_ind_mut, jcs_ind_mut, jbTs_ind_mut, jiqs_ind_mut.


  Derive Inversion j_q_sel_sem with (forall d G s b tml btb c Ssel, j_q_sem d G s (select b tml btb c) Ssel) Sort Prop.
  Derive Inversion j_q_selstar_sem with (forall d G s b btb c Sss, j_q_sem d G s (selstar b btb c) Sss) Sort Prop.
  Derive Inversion j_q_union_sem with (forall d G s b q1 q2 Sq, j_q_sem d G s (qunion b q1 q2) Sq) Sort Prop.
  Derive Inversion j_q_inters_sem with (forall d G s b q1 q2 Sq, j_q_sem d G s (qinters b q1 q2) Sq) Sort Prop.
  Derive Inversion j_q_except_sem with (forall d G s b q1 q2 Sq, j_q_sem d G s (qexcept b q1 q2) Sq) Sort Prop.
  Derive Inversion j_tb_base_sem with (forall d G s x ST, j_tb_sem d G s (tbbase x) ST) Sort Prop.
  Derive Inversion j_tb_query_sem with (forall d G s q ST, j_tb_sem d G s (tbquery q) ST) Sort Prop.
  Derive Inversion j_cons_btb_sem with (forall d G G' T s tl Scons, j_btb_sem d G G' ((T,s)::tl) Scons) Sort Prop.
  Derive Inversion j_iq_sel_sem with (forall d G b tml btb c Ssel, j_in_q_sem d G (select b tml btb c) Ssel) Sort Prop.
  Derive Inversion j_iq_selstar_sem with (forall d G b btb c Sss, j_in_q_sem d G (selstar b btb c) Sss) Sort Prop.
  Derive Inversion j_iq_union_sem with (forall d G b q1 q2 Sq, j_in_q_sem d G (qunion b q1 q2) Sq) Sort Prop.
  Derive Inversion j_iq_inters_sem with (forall d G b q1 q2 Sq, j_in_q_sem d G (qinters b q1 q2) Sq) Sort Prop.
  Derive Inversion j_iq_except_sem with (forall d G b q1 q2 Sq, j_in_q_sem d G (qexcept b q1 q2) Sq) Sort Prop.

  Lemma j_nil_btb_sem :
    forall d G G' Snil (P : Prop),
       (forall (G0 G0': Ctx), G0 = G -> G0' = G' -> List.nil = G0' ->
        (fun (_:Ev.env G) => Rel.Rone) ~= Snil -> P) ->
       j_btb_sem d G G' List.nil Snil -> P.
  Proof.
    intros.
    enough (forall G0 G0' (btb0 : list (pretb * Scm)) 
      (Snil0 : Ev.env G0 -> Rel.R (list_sum (List.map (length (A:=Name)) G0'))), 
        j_btb_sem d G0 G0' btb0 Snil0 ->
        G0 = G -> G0' = G' -> List.nil = btb0 -> Snil0 ~= Snil -> P).
    apply (H1 _ _ _ _ H0 eq_refl eq_refl eq_refl JMeq_refl).
    intros G0 G0' btb0 Snil0 H0'.
    destruct H0'; intros. eapply H; auto. rewrite H1 in H4. exact H4.
    discriminate H5.
  Qed.

  Theorem j_sem_fun : forall d,
    (forall G s q Sq, j_q_sem d G s q Sq -> forall s0 Sq0, j_q_sem d G s0 q Sq0 -> s = s0 /\ Sq ~= Sq0) /\
    (forall G s T ST, j_tb_sem d G s T ST -> forall s0 ST0, j_tb_sem d G s0 T ST0 -> s = s0 /\ ST ~= ST0) /\
    (forall G c Sc, j_cond_sem d G c Sc -> forall Sc0, j_cond_sem d G c Sc0 -> Sc ~= Sc0) /\
    (forall G G' btb Sbtb, j_btb_sem d G G' btb Sbtb -> 
      forall G0' Sbtb0, j_btb_sem d G G0' btb Sbtb0 -> G' = G0' /\ Sbtb ~= Sbtb0) /\
    (forall G q Sq, j_in_q_sem d G q Sq -> forall Sq0, j_in_q_sem d G q Sq0 -> Sq ~= Sq0).
  Proof.
    intro. apply j_sem_ind_mut.
    (* query *)
    + intros.
      (* the Coq refiner generates an ill-typed term if we don't give enough parameters to this eapply *)
      eapply (j_q_sel_sem _ _ _ _ _ _ _ _ (fun _ _ s1 _ _ _ _ Ssel =>
        _ = s1 /\ (fun h =>
        let S1 := Sbtb h in
        let p := fun Vl => is_btrue (Sc (Ev.env_app G0 G (Ev.env_of_tuple G0 Vl) h)) in
        let S2 := Rel.sel S1 p in
        let f := fun Vl => Stml (Ev.env_app G0 G (Ev.env_of_tuple G0 Vl) h) in
        let S := cast _ _ e (Rel.sum S2 f) in
        if b then Rel.flat S else S) ~= Ssel) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H13); clear H13; intros; subst.
      clear H3 H12. apply (existT_eq_elim (JMeq_eq H4)); clear H4; intros; subst.
      clear H3. destruct (H _ _ H5); subst. pose (H11 := H0 _ H9); clearbody H11. 
      rewrite H4.
      rewrite H11.
      replace e0 with e. replace Stml0 with Stml.
      split; reflexivity. apply (Ev.j_tml_sem_fun _ _ _ j1 _ H10). apply UIP.
    + intros. eapply (j_q_selstar_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ _ => _) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H12); clear H12; intros; subst.
      clear H3 H11. apply (existT_eq_elim (JMeq_eq H4)); clear H4; intros; subst.
      clear H3. destruct (H _ _ H6); subst. pose (H10 := H0 _ H8); clearbody H10. 
      rewrite H4, H10. replace e0 with e. replace Stml0 with Stml.
      split; reflexivity. apply (Ev.j_tml_sem_fun _ _ _ j1 _ H9). apply UIP.
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
      replace St0 with St. reflexivity. apply (Ev.j_tm_sem_fun _ _ _ j _ H2).
    + intros. inversion H. apply (existT_eq_elim H3); clear H3; intros; subst.
      apply (existT_eq_elim H5); clear H5; intros; subst. 
      replace e0 with (@eq_refl _ (length tml)).
      replace Stml0 with Stml. reflexivity.
      apply (Ev.j_tml_sem_fun _ _ _ j _ H2). apply UIP.
    + intros. inversion H0. apply (existT_eq_elim H6); clear H6; intros; subst. clear H6.
      destruct (H _ _ H7). subst. rewrite H2.
      replace Stml0 with Stml. replace e'0 with e'. reflexivity.
      apply UIP. apply (Ev.j_tml_sem_fun _ _ _ j _ H4).
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
    (* inner query *)
    + intros. eapply (j_iq_sel_sem _ _ _ _ _ _ _ (fun _ _ _ _ _ _ Ssel =>
        (fun h =>
         let S1 := Sbtb h in
         let p := fun Vl => is_btrue (Sc (Ev.env_app G0 G (Ev.env_of_tuple G0 Vl) h)) in
         let S2 := Rel.sel S1 p in
         let f := fun Vl => Stml (Ev.env_app G0 G (Ev.env_of_tuple G0 Vl) h) in
         let S := Rel.sum S2 f in 
         0 <? Rel.card (if b then Rel.flat S else S)) ~= Ssel) _ H1). Unshelve.
      intros; simpl; subst. apply (existT_eq_elim H11); clear H11; intros; subst.
      clear H2 H3. destruct (H _ _ H4); subst. pose (H9 := H0 _ H7); clearbody H9. 
      rewrite H3, H9. replace Stml0 with Stml. reflexivity.
      apply (Ev.j_tml_sem_fun _ _ _ j1 _ H8).
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
    (forall G q Sq, j_in_q_sem d G q Sq -> 
      forall G0 q0 Sq0, G = G0 -> q = q0 -> j_in_q_sem d G0 q0 Sq0 -> Sq ~= Sq0).
  Proof.
    intro. decompose [and] (j_sem_fun d). split.
      intros. subst. apply (H _ _ _ _ H3 _ _ H7).
    split.
      intros. subst. apply (H1 _ _ _ _ H3 _ _ H7).
    split.
      intros. subst. apply (H0 _ _ _ H3 _ H7).
    split.
      intros. subst. apply (H2 _ _ _ _ H3 _ _ H7).
    intros. subst. apply (H4 _ _ _ H3 _ H7).
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

(*
  Fixpoint q_sem d G Q s (HWF: j_query d G Q s) (h : env G) {struct HWF}
    : Db.Rel.R (List.length s)
  with tb_sem d G (x : bool) T s (HWF : j_tb d G T s) (h : env G) {struct HWF}
    : Db.Rel.R (List.length s)
  with cond_sem d G c (HWF : j_cond d G c) (h : env G) {struct HWF}
    : B
  with btb_sem d G btb G1 (HWF : j_btb d G btb G1) (h : env G) {struct HWF}
    : Db.Rel.R (List.length (List.concat G1))
  with inner_q_sem d G Q (HWF: j_inquery d G Q) (h : env G) {struct HWF}
    : bool.
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
        let p := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) => 
          Sem.is_btrue (cond_sem _ _ _ j0 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h)) in
        let S2 := Db.Rel.sel S1 (cast _ _ _ p) in _).
      refine (let f := fun (Vl : Db.Rel.T (list_sum (List.map (length (A:=Name)) c0))) =>
        v_tml_sem _ _ j1 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h) in _).
      case (sumbool_of_bool b); intro.
      - (* DISTINCT *)
        eapply Db.Rel.flat. eapply (Db.Rel.sum S2). eapply (cast _ _ _ f).
        Unshelve.
        ** rewrite length_concat_list_sum. reflexivity.
        ** repeat rewrite cmap_length. rewrite length_concat_list_sum. reflexivity.
      - eapply (Db.Rel.sum S2). eapply (cast _ _ _ f).
        Unshelve.
        repeat rewrite cmap_length. rewrite length_concat_list_sum. reflexivity.
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
    + refine (of_bool (inner_q_sem _ _ _ j h)).
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
  * refine ((match HWF in (j_inquery _ G0 Q0) return (G = G0 -> Q = Q0 -> bool) with
        | j_inselect _ _ _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_inselstar _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_inunion _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_ininters _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        | j_inexcept _ _ _ _ _ _ _ _ => fun eqG eqQ => _
        end)
      eq_refl eq_refl).
    all: subst.
    + refine (let S1 := btb_sem _ _ _ _ j h in
        let p := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) => 
          Sem.is_btrue (cond_sem _ _ _ j0 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h)) in
        let S2 := Db.Rel.sel S1 (cast _ _ _ p) in _).
      refine (let f := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) =>
        v_tml_sem _ _ j1 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h) in _).
(*  we don't need all this: whether it's distinct or not, it's the same cardinality
      exists (List.length (List.map fst l)).
      case (sumbool_of_bool b); intro.
      - (* DISTINCT *)
        eapply Db.Rel.flat. eapply (Db.Rel.sum S2).
        eapply (cast _ _ _ f). Unshelve. rewrite length_concat_list_sum. reflexivity.
      - eapply (Db.Rel.sum S2). eapply (cast _ _ _ f). Unshelve. rewrite length_concat_list_sum. reflexivity.
*)    
      refine (0 <? Rel.card (Rel.sum S2 (cast _ _ _ f))). Unshelve.
      - rewrite length_concat_list_sum. reflexivity.
      - rewrite length_concat_list_sum. reflexivity.
    + refine (let S1 := btb_sem _ _ _ _ j h in
        let p := fun (Vl : Db.Rel.T (list_sum (List.map (@length Name) c0))) => 
          Sem.is_btrue (cond_sem _ _ _ j0 (Ev.env_app _ _ (Ev.env_of_tuple c0 Vl) h))
        in
        let S2 := Db.Rel.sel S1 (cast _ _ _ p) in _). Unshelve. Focus 2.
      rewrite length_concat_list_sum. reflexivity.
      refine (let f := fun (_ : Db.Rel.T (list_sum (List.map (@length Name) c0))) =>
        Vector.nil Rel.V in _).
(*
      exists 0.
      case (sumbool_of_bool b); intro.
      - (* DISTINCT *)
        eapply Db.Rel.flat. eapply (Db.Rel.sum S2). intro. apply f.
        rewrite <- length_concat_list_sum. apply X.
      - eapply (Db.Rel.sum S2). intro. apply f. rewrite <- length_concat_list_sum. apply X.
*)
      refine (0 <? Rel.card (Rel.sum S2 (cast _ _ _ f))). Unshelve.
      rewrite length_concat_list_sum. reflexivity.
(*
    + exists (List.length s). case (sumbool_of_bool b); intro.
      - apply (Db.Rel.plus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.flat (Db.Rel.plus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    + exists (List.length s). case (sumbool_of_bool b); intro.
      - apply (Db.Rel.inter (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.flat (Db.Rel.inter (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    + exists (List.length s). case (sumbool_of_bool b); intro.
      - apply (Db.Rel.minus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h)).
      - apply (Db.Rel.minus (Db.Rel.flat (q_sem _ _ _ _ j h)) (q_sem _ _ _ _ j0 h)).
*)
    + refine (((0 <? Rel.card (q_sem _ _ _ _ j h)) || (0 <? Rel.card (q_sem _ _ _ _ j0 h)))%bool).
    + refine (0 <? Rel.card (Rel.inter (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    + refine (0 <? Rel.card (Rel.minus (q_sem _ _ _ _ j h) (q_sem _ _ _ _ j0 h))).
    Defined.
*)
  Lemma eq_rect_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect x P p x eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_rect_r_eq_refl {A x} {P : A -> Type} {p : P x} : eq_rect_r P p eq_refl = p. 
  reflexivity.
  Qed.
  Lemma eq_JMeq {A} {x y : A} (H : x = y) : x ~= y.
  rewrite H. reflexivity.
  Qed.

(*
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
      f_equal. apply JMeq_eq. apply IHc. rewrite H5. reflexivity.
      f_equal. extensionality Vl.
      apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H5. reflexivity.
    - apply eq_JMeq. f_equal. f_equal. f_equal. f_equal. extensionality Vl.
      f_equal. apply JMeq_eq. apply IHc. rewrite H5. reflexivity.
      f_equal. extensionality Vl.
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
    apply eq_JMeq. f_equal. f_equal. f_equal.
    - f_equal. f_equal. extensionality Vl. f_equal. apply JMeq_eq. apply IHc.
      rewrite H0. reflexivity.
    - f_equal. extensionality Vl. apply JMeq_eq. apply Ev.v_tml_sem_pi. rewrite H0. reflexivity.
  + intros G btb G' c x Hbtb IHbtb Hc IHc j' h .
    dependent inversion j' with 
      (fun G0 Q0 Hinv => forall h', h ~= h' ->
        inner_q_sem d G (selstar x btb c) (j_inselstar d G btb G' c x Hbtb Hc) h ~=
          inner_q_sem d G0 Q0 Hinv h').
    intros. destruct (IHbtb _ _ j _ H0).
    generalize j, j0, H5. clear j j0 H5. rewrite <- H4.
    intros. simpl. repeat rewrite eq_rect_r_eq_refl. repeat rewrite H5. rewrite H0.
    apply eq_JMeq. f_equal. f_equal. f_equal. f_equal. f_equal. extensionality Vl.
    f_equal. apply JMeq_eq. apply IHc. reflexivity.
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

*)

End SQLSemantics.