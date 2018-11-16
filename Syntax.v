Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat AbstractRelation Tribool.

Definition ret {A} : A -> option A := Some.
Definition bind {A B} : option A -> (A -> option B) -> option B :=
  fun a f => match a with None => None | Some x => f x end.
Definition monadic_map {A B} (f : A -> option B) (l : list A) : option (list B) :=
  List.fold_right (fun a mbl => 
    bind mbl (fun bl => 
    bind (f a) (fun b => 
    ret (b::bl))))
  (ret List.nil) l.

Lemma length_monadic_map (A B: Type) (f : A -> option B) (l1 : list A) :
  forall l2, monadic_map f l1 = Some l2 -> List.length l1 = List.length l2.
elim l1.
+ intro. simpl. unfold ret. intro. injection H. intro. subst. auto.
+ simpl. intros a l. case (monadic_map f l).
  - simpl. case (f a).
    * simpl. unfold ret. intros b l0 IH l2 Hl2. injection Hl2. intro H.
      subst. simpl. apply f_equal. apply IH. reflexivity.
    * simpl. intros. discriminate.
  - simpl. intros. discriminate.
Qed.

Lemma bind_elim (A B : Type) (x : option A) (f : A -> option B) (P : option B -> Prop) :
  (forall y, x = Some y -> P (f y)) -> (x = None -> P None) ->
  P (bind x f).
intros. destruct x eqn:e; simpl; auto.
Qed.

Lemma length_to_list (A : Type) (n : nat) (v : Vector.t A n) : length (to_list v) = n.
elim v. auto.
intros. transitivity (S (length (to_list t ))); auto.
Qed.

Definition vec_monadic_map {A B n} (f : A -> option B) (v : Vector.t A n) : option (Vector.t B n).
Proof.
  destruct (monadic_map f (Vector.to_list v)) eqn:e.
  + refine (Some (cast (of_list l) _)).
    refine (let Hlen := length_monadic_map _ _ _ _ _ e in _).
    rewrite <- Hlen.
    apply length_to_list.
  + apply None.
Qed.

Module Type DB.
  Parameter Name : Type.
  Hypothesis Name_dec : forall x y:Name, {x = y} + {x <> y}. 
  Definition FullName := (Name * Name)%type.
  Definition FullVar  := (nat * Name)%type.
  Definition Scm      := list Name.         (* schema (attribute names for a relation) *)
  Definition Ctx      := list Scm.          (* context (domain of an environment) = list of lists of names *)

  Parameter BaseConst : Type.
  Definition Value    := option BaseConst.
  Definition null     : Value := None.
  Definition c_sem     : BaseConst -> Value := Some.    (* semantics of constants *)

  Declare Module Rel  : REL with Definition V := Value.

  Parameter D         : Type.
  Variable db_schema  : D -> Name -> option (list Name).
  Hypothesis db_rel   : forall d n xl, db_schema d n = Some xl -> Rel.R (List.length xl).
  Implicit Arguments db_rel [d n xl].

  Lemma Scm_dec (s1 s2 : Scm) : {s1 = s2} + {s1 <> s2}.
    exact (list_eq_dec Name_dec s1 s2).
  Qed.

  Definition Scm_eq : Scm -> Scm -> bool := 
    fun s1 s2 => match Scm_dec s1 s2 with left _ => true | right _ => false end.

  Lemma Scm_eq_elim (P : bool -> Prop) (s s' : Scm) (Htrue : s = s' -> P true) (Hfalse : s <> s' -> P false)
  : P (Scm_eq s s').
  unfold Scm_eq. destruct (Scm_dec s s') eqn:e. all: auto.
  Qed.


  Lemma FullName_dec (A B : FullName) : {A = B} + {A <> B}.
    elim A; intros A1 A2.
    elim B; intros B1 B2.
    elim (Name_dec A1 B1); intro H1.
    + elim (Name_dec A2 B2); intro H2.
      - subst. left. reflexivity.
      - right. intro. injection H. intro. contradiction H2.
    + right. intro. injection H. intros _ H2. contradiction H1.
  Qed.

  Definition FullName_eq : FullName -> FullName -> bool :=
    fun A B => match FullName_dec A B with left _ => true | right _ => false end.

  Parameter c_eq : BaseConst -> BaseConst -> bool.
  Hypothesis BaseConst_dec : forall (c1 c2 : BaseConst), { c1 = c2 } + { c1 <> c2 }.
  Hypothesis BaseConst_eqb_eq : forall (c1 c2 : BaseConst), c_eq c1 c2 = true <-> c1 = c2.

End DB.

Module Type SQL (Db : DB).
  Import Db.

  (* I will probably need to declare a canonical structure/type class for Names *)

  Inductive pretm : Type :=
  | tmconst : BaseConst -> pretm
  | tmnull  : pretm
  | tmvar   : FullVar -> pretm    (* refers to FROM tables *)
  .

  Lemma pretm_dec : forall (x y: pretm), { x = y } + { x <> y }.
  Proof.
    decide equality. apply Db.BaseConst_dec. decide equality. apply Db.Name_dec. apply Nat.eq_dec.
  Qed.

  Inductive prequery : Type :=
  | select  : bool -> list (pretm * Name) -> list (pretb * Scm) -> precond -> prequery
  | selstar : bool -> list (pretb * Scm) -> precond -> prequery
  | qunion  : bool -> prequery -> prequery -> prequery
  | qinters : bool -> prequery -> prequery -> prequery
  | qexcept : bool -> prequery -> prequery -> prequery

  with precond : Type :=
  | cndtrue   : precond
  | cndfalse  : precond
  | cndnull   : bool -> pretm -> precond
  | cndpred   : forall n, (forall l : list BaseConst, length l = n -> bool) -> list pretm -> precond
  | cndmemb   : bool -> list pretm -> prequery -> precond
  | cndex     : prequery -> precond
  | cndand    : precond -> precond -> precond
  | cndor     : precond -> precond -> precond
  | cndnot    : precond -> precond

  with pretb: Type :=
  | tbbase  : Name -> pretb
  | tbquery : prequery -> pretb.

  Notation "'NULL'" := (tmnull) (at level 45).

  Notation "'SELECT' btm 'FROM' btb 'WHERE' c" := (select false btm btb c) (at level 45).
  Notation "'SELECT' 'DISTINCT' btm 'FROM' btb 'WHERE' c" := (select true btm btb c) (at level 45).
  Notation "'SELECT' '*' 'FROM' btb 'WHERE' c" := (selstar false btb c) (at level 45).
  Notation "'SELECT' 'DISTINCT' '*' 'FROM' btb 'WHERE' c" := (selstar true btb c) (at level 45).
  Notation "Q1 'UNION' Q2" := (qunion false Q1 Q2) (at level 45).
  Notation "Q1 'INTERSECT' Q2" := (qinters false Q1 Q2) (at level 45).
  Notation "Q1 'EXCEPT' Q2" := (qexcept false Q1 Q2) (at level 45).
  Notation "Q1 'UNION' 'ALL' Q2" := (qunion true Q1 Q2) (at level 45).
  Notation "Q1 'INTERSECT' 'ALL' Q2" := (qinters true Q1 Q2) (at level 45).
  Notation "Q1 'EXCEPT' 'ALL' Q2" := (qexcept true Q1 Q2) (at level 45).

  Notation "'FALSE'" := cndfalse (at level 45).
  Notation "'TRUE'" := cndtrue (at level 45).
  Notation "t 'IS' 'NULL'" := (cndnull true t) (at level 45).
  Notation "t 'IS' 'NOT' 'NULL'" := (cndnull false t) (at level 45).
  Notation "tl 'IN' Q" := (cndmemb true tl Q) (at level 45).
  Notation "tl 'NOT' 'IN' Q" := (cndmemb false tl Q) (at level 45).
  Notation "'EXISTS' Q" := (cndex Q) (at level 45).
  Notation "e1 'AND' e2" := (cndand e1 e2) (at level 45).
  Notation "e1 'OR' e2" := (cndor e1 e2) (at level 45).
  Notation "'NOT' e" := (cndnot e) (at level 45).

  Definition mapi {A B: Type} (f : nat -> A -> B) (l : list A) : list B := 
    (fix aux l0 i : list B :=
      match l0 with
      | List.nil => List.nil
      | a::tl => f i a::aux tl (S i)
      end) l 0.

  Definition btm_of_ctx (G: Ctx) : list (pretm * Name) := 
    List.concat (mapi (fun i => List.map (fun x => (tmvar (i,x), x))) G).

  Definition tmlist_of_ctx (G: Ctx) : list pretm := 
    List.concat (mapi (fun i => List.map (fun x => tmvar (i,x))) G).

  Inductive j_var (a : Name) : Scm -> Prop :=
  | j_varhd   : forall s, ~ List.In a s -> j_var a (a::s)
  | j_varcons : forall b s, a <> b -> j_var a s -> j_var a (b::s).

  Inductive j_tm  (g : Ctx) : pretm -> Prop := 
  | j_const : forall c, j_tm g (tmconst c)
  | j_null  : j_tm g tmnull
  | j_tmvar : forall n a s, List.nth_error g n = Some s -> j_var a s -> j_tm g (tmvar (n,a)).

  Inductive j_db (d : Db.D) : Prop := .

  Definition j_tml (g : Ctx) (tl : list pretm) : Type := forall t, List.In t tl -> j_tm g t.

  Variable dflist : forall A, list A -> Prop.

  Inductive j_query (d : Db.D) : Ctx -> prequery -> Scm -> Prop :=
  | j_select :
      forall s c b btm btb g g1,
      j_btb d g btb g1 ->       (* btb is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->   (* c is defined under Ctx (g1 ++ g) *)
      j_tml (g1 ++ g) (List.map fst btm) -> (* the attr names given don't matter *)
      (* j_tm/j_cond needs all of the references to be unambiguous, i.e. if (g1 ++ g) contains duplicate entries,
          they cannot be used by the terms *)
      s = List.map snd btm ->   (* the schema is given by the second components of btm *)
      j_query d g (select b btm btb c) s
  | j_selstar :
      forall g btb g1 c s b,
      j_btb d g btb g1 ->       (* btb is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->   (* c is defined under Ctx (g1 ++ g) *)
      s = List.concat g1 ->     (* merges the schemas in g1 *)
      j_tml (g1 ++ g) (tmlist_of_ctx g1) ->
      (* the line above forces the attributes in g1 to be unambiguous *)
      j_query d g (selstar b btb c) s
  | j_union   : forall g b q1 q2 s, j_query d g q1 s -> j_query d g q2 s -> j_query d g (qunion b q1 q2) s
  | j_inters  : forall g b q1 q2 s, j_query d g q1 s -> j_query d g q2 s -> j_query d g (qinters b q1 q2) s
  | j_except  : forall g b q1 q2 s, j_query d g q1 s -> j_query d g q2 s -> j_query d g (qexcept b q1 q2) s

  with j_tb (d : Db.D) : Ctx -> pretb -> Scm -> Prop :=
  | j_tbbase  : forall x s g, j_db d -> Db.db_schema d x = Some s -> j_tb d g (tbbase x) s
  | j_tbquery : forall g q s, j_query d g q s -> j_tb d g (tbquery q) s

  with j_cond (d : Db.D) : Ctx -> precond -> Prop :=
  | j_cndtrue   : forall g, j_db d -> j_cond d g cndtrue
  | j_cndfalse  : forall g, j_db d -> j_cond d g cndfalse
  | j_cndnull   : forall g t b, j_db d -> j_tm g t -> j_cond d g (cndnull b t)
  | j_cndpred   : forall g n p tml, j_db d -> j_tml g tml -> length tml = n -> j_cond d g (cndpred n p tml)
  | j_cndmemb   : forall g q sq tl b, 
                  j_tml g tl -> j_query d g q sq -> 
                  List.length sq = List.length tl -> j_cond d g (cndmemb b tl q)
  | j_cndex     : forall g q, j_inquery d g q -> j_cond d g (cndex q)
  | j_cndand    : forall g c1 c2, j_cond d g c1 -> j_cond d g c2 -> j_cond d g (cndand c1 c2)
  | j_cndor     : forall g c1 c2, j_cond d g c1 -> j_cond d g c2 -> j_cond d g (cndor c1 c2)
  | j_cndnot    : forall g c, j_cond d g c -> j_cond d g (cndnot c)

  (* the output of j_btb can use any choice of names, avoiding collision *)
  with j_btb  (d : Db.D) : Ctx -> list (pretb * Scm) -> Ctx -> Prop :=
  | j_btbnil  : forall g, j_db d -> j_btb d g List.nil List.nil
  | j_btbcons : forall g T s s' btb g1, length s = length s' -> List.NoDup s' -> 
                j_tb d g T s -> j_btb d g btb g1 -> j_btb d g ((T,s')::btb) (s'::g1)

  with j_inquery (d : Db.D) : Ctx -> prequery -> Prop :=
  | j_inselect :
      forall c b btm btb g g1,
      j_btb d g btb g1 ->       (* btb is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->  (* c is defined under Ctx (g (+) g1) *)
      j_tml (g1 ++ g) (List.map fst btm) -> (* btm is wellformed under Ctx (g (+) g1) *)
      j_inquery d g (select b btm btb c)
  | j_inselstar :
      forall g btb g1 c b,
      j_btb d g btb g1 ->       (* btb is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->  (* c is defined under Ctx (g (+) g1) *)
      (* the different behaviour, compared with j_query, is achieved by omitting the j_tml premise *)
      j_inquery d g (selstar b btb c)
  | j_inunion   : forall g b q1 q2 s, j_query d g q1 s -> j_query d g q2 s -> j_inquery d g (qunion b q1 q2)
  | j_ininters  : forall g b q1 q2 s, j_query d g q1 s -> j_query d g q2 s -> j_inquery d g (qinters b q1 q2)
  | j_inexcept  : forall g b q1 q2 s, j_query d g q1 s -> j_query d g q2 s -> j_inquery d g (qexcept b q1 q2)
  .

  Scheme jq_ind_mut := Induction for j_query Sort Prop
  with jT_ind_mut := Induction for j_tb Sort Prop
  with jc_ind_mut := Induction for j_cond Sort Prop
  with jbT_ind_mut := Induction for j_btb Sort Prop
  with jiq_ind_mut := Induction for j_inquery Sort Prop.

  Combined Scheme j_ind_mut from jq_ind_mut, jT_ind_mut, jc_ind_mut, jbT_ind_mut, jiq_ind_mut.

  Definition tm := fun G => { t : pretm & j_tm G t }.
  Definition query := fun d G s => { Q : prequery & j_query d G Q s }.
  Definition tb := fun d G s => { T : pretb & j_tb d G T s }.
  Definition cond := fun d G => { c : precond & j_cond d G c }.
  Definition inquery := fun d G => { Q : prequery & j_inquery d G Q }.

  (* a recursive definition of schemas *)

  (* XXX: not entirely sure of the rationale for propagating or erasing the boolean b *)
  Fixpoint q_schema (d : Db.D) (q : prequery) (b : bool) {struct q} : option (list Name) :=
    match q with
    | select _ btm _ _  => ret (List.map snd btm) (* XXX: no duplicate-freedom check *)
    | selstar _ btb _   =>
        if b then ret List.nil
        else ret (List.concat (List.map snd btb))
     (* bind (monadic_map (tb_schema d) btb) (fun G0 => ret (List.concat G0)) *)
    | qunion _ q1 q2    =>
        bind (q_schema d q1 false) (fun sq1 =>
        bind (q_schema d q2 false) (fun sq2 =>
          if (Scm_eq sq1 sq2) then ret sq1 else None))
    | qinters _ q1 q2   =>
        bind (q_schema d q1 false) (fun sq1 =>
        bind (q_schema d q2 false) (fun sq2 =>
          if (Scm_eq sq1 sq2) then ret sq1 else None))
    | qexcept _ q1 q2   => 
        bind (q_schema d q1 false) (fun sq1 =>
        bind (q_schema d q2 false) (fun sq2 =>
          if (Scm_eq sq1 sq2) then ret sq1 else None))
    end
  with tb_schema (d : Db.D) (T : pretb) {struct T} : option (list Name) :=
    match T with
    | tbbase x  => Db.db_schema d x
    | tbquery q0 => q_schema d q0 false
    end
  with pred_safe (d : Db.D) (c : precond) {struct c} : bool :=
    match c with
    | cndmemb _ tl q0 => 
        match (q_schema d q0 false) with Some sq0 => List.length sq0 =? List.length tl | _ => false end
    | cndex q0 => match q_schema d q0 true with None => false | _ => true end
    | cndand c1 c2 => pred_safe d c1 && pred_safe d c2
    | cndor c1 c2 => pred_safe d c1 && pred_safe d c2
    | cndnot c0 => pred_safe d c0
    | cndpred n p tml => length tml =? n
    | _ => true
    end.

  Definition btb_schema (d : Db.D) (btb : list (pretb * Scm)) : option Ctx :=
    (* bind (monadic_map (tb_schema d) btb) ret *)
    ret (List.map snd btb).

  Theorem jq_q_schema : forall d G Q s,
    forall j : j_query d G Q s, q_schema d Q false = Some s.
  intros d G Q s HWF.
  eapply (jq_ind_mut _ 
          (fun G0 Q0 s0 H0 => q_schema d Q0 false = Some s0)
          (fun G0 T0 s0 H0 => tb_schema d T0 = Some s0)
          (fun G0 c0 H0 => pred_safe d c0 = true)
          (fun G0 btb G1 H0 => btb_schema d btb = Some G1)
          (fun G0 Q0 H0 => exists s0, q_schema d Q0 true = Some s0)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF).
  Unshelve.
  + intros s0 c b btm btb G0 G1 Hbtb IHbtb Hc IHc Html. simpl. intro. rewrite e. reflexivity.
  + intros G0 btb G1 c s0 b Hbtb IHbtb Hc IHc e Html. simpl. 
    simpl in IHbtb. unfold btb_schema, ret in IHbtb. injection IHbtb. clear IHbtb; intro IHbtb.
    rewrite e. rewrite IHbtb. reflexivity.
  + intros G0 b Q1 Q2 s0 HQ1 IHQ1 HQ2 IHQ2; simpl; rewrite IHQ1, IHQ2; simpl; apply Scm_eq_elim; intro H;
    [ reflexivity | contradiction H; reflexivity ].
  + intros G0 b Q1 Q2 s0 HQ1 IHQ1 HQ2 IHQ2; simpl; rewrite IHQ1, IHQ2; simpl; apply Scm_eq_elim; intro H;
    [ reflexivity | contradiction H; reflexivity ].
  + intros G0 b Q1 Q2 s0 HQ1 IHQ1 HQ2 IHQ2; simpl; rewrite IHQ1, IHQ2; simpl; apply Scm_eq_elim; intro H;
    [ reflexivity | contradiction H; reflexivity ].
  + intros x s0 G0 Hdb e. simpl. exact e.
  + intros x s0 G0 Hdb e. simpl. exact e.
  + intros G0 Hdb. reflexivity.
  + intros G0 Hdb. reflexivity.
  + intros G0 t b Hdb Ht. reflexivity.
  + intros G0 n p tml Hdb Html e. simpl. apply Nat.eqb_eq. exact e.
  + intros G0 Q0 sQ tl b Html HQ0 IHQ0 e. simpl. rewrite IHQ0. apply Nat.eqb_eq. exact e.
  + intros G0 Q0 HQ0 IHQ0. simpl. destruct IHQ0. rewrite H. reflexivity.
  + intros G0 c1 c2 Hc1 IHc1 Hc2 IHc2. simpl. rewrite IHc1, IHc2. reflexivity.
  + intros G0 c1 c2 Hc1 IHc1 Hc2 IHc2. simpl. rewrite IHc1, IHc2. reflexivity.
  + intros G0 c0 Hc0 IHc0. simpl. rewrite IHc0. reflexivity.
  + intros G0 Hdb. reflexivity.
  + intros G0 T s0 s' btb G1 Hlen Hnodup HT IHT Hbtb IHbtb. simpl. unfold btb_schema. simpl.
    simpl in IHbtb. unfold btb_schema, ret in IHbtb. injection IHbtb. clear IHbtb; intro IHbtb.
    rewrite IHbtb. reflexivity.
  + intros c b btm btb G0 G1 Hbtb IHbtb Hc IHc Html. simpl. eexists. all:auto.
  + intros G0 btb G1 c b Hbtb IHbtb Hc IHc. simpl. eexists. all:eauto.
  + intros G0 b Q1 Q2 s0 HQ1 IHQ1 HQ2 IHQ2; simpl; rewrite IHQ1, IHQ2; simpl; 
    exists s0; apply Scm_eq_elim; intro H; [ reflexivity | contradiction H; reflexivity ].
  + intros G0 b Q1 Q2 s0 HQ1 IHQ1 HQ2 IHQ2; simpl; rewrite IHQ1, IHQ2; simpl; 
    exists s0; apply Scm_eq_elim; intro H; [ reflexivity | contradiction H; reflexivity ].
  + intros G0 b Q1 Q2 s0 HQ1 IHQ1 HQ2 IHQ2; simpl; rewrite IHQ1, IHQ2; simpl; 
    exists s0; apply Scm_eq_elim; intro H; [ reflexivity | contradiction H; reflexivity ].
  Qed.

  Definition tm_lift (t : pretm) k :=
    match t with
    | tmvar x => let (n,a) := x in tmvar (k+n,a)
    | _ => t
    end.

  Lemma j_tm_weak G G' t : j_tm G t -> j_tm (G' ++ G) (tm_lift t (length G')).
  Proof.
    intro H. elim H; try (intros; constructor).
    simpl. intros n a s HG Has. eapply (j_tmvar _ _ _ s); auto.
    elim G'; auto.
  Qed.

End SQL.