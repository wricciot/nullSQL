Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat AbstractRelation Tribool Common Util.

Module Type SQL.
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
  | select  : bool -> list (pretm * Name) -> list (list (pretb * Scm)) -> precond -> prequery
  | selstar : bool -> list (list (pretb * Scm)) -> precond -> prequery
  | qunion  : bool -> prequery -> prequery -> prequery
  | qinters : bool -> prequery -> prequery -> prequery
  | qexcept : bool -> prequery -> prequery -> prequery

  with precond : Type :=
  | cndtrue   : precond
  | cndfalse  : precond
  | cndnull   : bool -> pretm -> precond
  | cndistrue : precond -> precond
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

  Lemma length_tmlist c0 : length (tmlist_of_ctx c0) = length (concat c0).
  Proof.
    unfold tmlist_of_ctx. unfold mapi. generalize 0.
    elim c0; intuition. 
    simpl. do 2 rewrite app_length. rewrite cmap_length.
    f_equal. apply H.
  Qed.

  Inductive j_var (a : Name) : Scm -> Prop :=
  | j_varhd   : forall s, ~ List.In a s -> j_var a (a::s)
  | j_varcons : forall b s, a <> b -> j_var a s -> j_var a (b::s).

  Inductive j_tm  (g : Ctx) : pretm -> Prop := 
  | j_const : forall c, j_tm g (tmconst c)
  | j_null  : j_tm g tmnull
  | j_tmvar : forall n a s, List.nth_error g n = Some s -> j_var a s -> j_tm g (tmvar (n,a)).

  (* this was put into place to allow for well-formedness conditions on the DB,
     but we don't have any *)
  Inductive j_db (d : Db.D) : Prop := jd_intro : j_db d.

  Definition j_tml (g : Ctx) (tl : list pretm) : Type := forall t, List.In t tl -> j_tm g t.

  Definition dflist : forall A, list A -> Prop := List.NoDup.

  Inductive j_query (d : Db.D) : Ctx -> prequery -> Scm -> Prop :=
  | j_select :
      forall s c b btm btbl g g1,
      j_btbl d g btbl g1 ->     (* btbl is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->   (* c is defined under Ctx (g1 ++ g) *)
      j_tml (g1 ++ g) (List.map fst btm) -> (* the attr names given don't matter *)
      (* j_tm/j_cond needs all of the references to be unambiguous, i.e. if (g1 ++ g) contains duplicate entries,
          they cannot be used by the terms *)
      s = List.map snd btm ->   (* the schema is given by the second components of btm *)
      j_query d g (select b btm btbl c) s
  | j_selstar :
      forall g btbl g1 c s b,
      j_btbl d g btbl g1 ->       (* btb is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->   (* c is defined under Ctx (g1 ++ g) *)
      s = List.concat g1 ->     (* merges the schemas in g1 *)
      j_tml (g1 ++ g) (tmlist_of_ctx g1) ->
      (* the line above forces the attributes in g1 to be unambiguous *)
      j_query d g (selstar b btbl c) s
  (* union etc. allow different schemas for subqueries, and return the schema of the first query *)
  | j_union   : forall g b q1 q2 s s', length s = length s' -> j_query d g q1 s -> j_query d g q2 s' -> j_query d g (qunion b q1 q2) s
  | j_inters  : forall g b q1 q2 s s', length s = length s' -> j_query d g q1 s -> j_query d g q2 s' -> j_query d g (qinters b q1 q2) s
  | j_except  : forall g b q1 q2 s s', length s = length s' -> j_query d g q1 s -> j_query d g q2 s' -> j_query d g (qexcept b q1 q2) s

  with j_tb (d : Db.D) : Ctx -> pretb -> Scm -> Prop :=
  | j_tbbase  : forall x s g, j_db d -> Db.db_schema d x = Some s -> j_tb d g (tbbase x) s
  | j_tbquery : forall g q s, j_query d g q s -> j_tb d g (tbquery q) s

  with j_cond (d : Db.D) : Ctx -> precond -> Prop :=
  | j_cndtrue   : forall g, j_db d -> j_cond d g cndtrue
  | j_cndfalse  : forall g, j_db d -> j_cond d g cndfalse
  | j_cndnull   : forall g t b, j_db d -> j_tm g t -> j_cond d g (cndnull b t)
  | j_cndistrue : forall g c, j_cond d g c -> j_cond d g (cndistrue c)
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

  with j_btbl (d : Db.D) : Ctx -> list (list (pretb * Scm)) -> Ctx -> Prop :=
  | j_btblnil : forall g, j_db d -> j_btbl d g List.nil List.nil
  | j_btblcons : forall g B Bl g1 g2, j_btbl d g Bl g1 -> j_btb d (g1++g) B g2 -> j_btbl d g (B::Bl) (g2++g1)
 
  with j_inquery (d : Db.D) : Ctx -> prequery -> Prop :=
  | j_inselect :
      forall c b btm btbl g g1,
      j_btbl d g btbl g1 ->       (* btb is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->  (* c is defined under Ctx (g (+) g1) *)
      j_tml (g1 ++ g) (List.map fst btm) -> (* btm is wellformed under Ctx (g (+) g1) *)
      j_inquery d g (select b btm btbl c)
  | j_inselstar :
      forall g btbl g1 c b,
      j_btbl d g btbl g1 ->       (* btb is wellformed under Ctx g, producing a context extension g1 *)
      j_cond d (g1 ++ g) c ->  (* c is defined under Ctx (g (+) g1) *)
      (* the different behaviour, compared with j_query, is achieved by omitting the j_tml premise *)
      j_inquery d g (selstar b btbl c)
  (* union etc. allow different schemas for subqueries, and return the schema of the first query *)
  | j_inunion   : forall g b q1 q2 s s', length s = length s' -> j_query d g q1 s -> j_query d g q2 s' -> j_inquery d g (qunion b q1 q2)
  | j_ininters  : forall g b q1 q2 s s', length s = length s' -> j_query d g q1 s -> j_query d g q2 s' -> j_inquery d g (qinters b q1 q2)
  | j_inexcept  : forall g b q1 q2 s s', length s = length s' -> j_query d g q1 s -> j_query d g q2 s' -> j_inquery d g (qexcept b q1 q2)
  .

  Scheme jq_ind_mut := Induction for j_query Sort Prop
  with jT_ind_mut := Induction for j_tb Sort Prop
  with jc_ind_mut := Induction for j_cond Sort Prop
  with jbT_ind_mut := Induction for j_btb Sort Prop
  with jbTl_ind_mut := Induction for j_btbl Sort Prop
  with jiq_ind_mut := Induction for j_inquery Sort Prop.

  Combined Scheme j_ind_mut from jq_ind_mut, jT_ind_mut, jc_ind_mut, jbT_ind_mut, jiq_ind_mut.

  Definition tm := fun G => { t : pretm & j_tm G t }.
  Definition query := fun d G s => { Q : prequery & j_query d G Q s }.
  Definition tb := fun d G s => { T : pretb & j_tb d G T s }.
  Definition cond := fun d G => { c : precond & j_cond d G c }.
  Definition inquery := fun d G => { Q : prequery & j_inquery d G Q }.

  (* a recursive definition of schemas *)

  (* XXX: not entirely sure of the rationale for propagating or erasing the boolean b *)
  Fixpoint q_schema (d : Db.D) (q : prequery) (b : bool) {struct q} : list Name :=
    match q with
    | select _ btm _ _  => List.map snd btm (* XXX: no duplicate-freedom check *)
    | selstar _ btb _   =>
        if b then List.nil
        else List.concat (List.concat ((List.map (List.map snd) btb)))
     (* bind (monadic_map (tb_schema d) btb) (fun G0 => ret (List.concat G0)) *)
    | qunion _ q1 _ => q_schema d q1 false
    | qinters _ q1 q2   => q_schema d q1 false
    | qexcept _ q1 q2   => q_schema d q1 false
    end.

  Definition tb_schema (d : Db.D) (T : pretb) : option (list Name) :=
    match T with
    | tbbase x  => Db.db_schema d x
    | tbquery q0 => ret (q_schema d q0 false)
    end.

(* 
  Fixpoint pred_safe (d : Db.D) (c : precond) {struct c} : bool :=
    match c with
    | cndmemb _ tl q0 => List.length (q_schema d q0 false) =? List.length tl
    | cndex q0 => match q_schema d q0 true with None => false | _ => true end
    | cndand c1 c2 => pred_safe d c1 && pred_safe d c2
    | cndor c1 c2 => pred_safe d c1 && pred_safe d c2
    | cndnot c0 => pred_safe d c0
    | cndpred n p tml => length tml =? n
    | _ => true
    end.
*)

  Definition btb_schema (d : Db.D) : list (pretb * Scm) -> Ctx :=
    (* bind (monadic_map (tb_schema d) btb) ret *)
    List.map snd.

  Definition btbl_schema (d : Db.D) (btbl : list (list (pretb * Scm))) : Ctx :=
    List.concat (List.map (btb_schema d) btbl).

(* TODO we stop here because we still have to do btbl_schema *)

  Theorem jq_q_schema : forall d G Q s,
    forall j : j_query d G Q s, q_schema d Q false = s.
  intros d G Q s HWF.
  eapply (jq_ind_mut _ 
          (fun G0 Q0 s0 H0 => q_schema d Q0 false = s0)
          (fun G0 T0 s0 H0 => (* tb_schema d T0 = Some s0 *) True)
          (fun G0 c0 H0 => (* pred_safe d c0 = true *) True)
          (fun G0 btb G1 H0 => btb_schema d btb = G1)
          (fun G0 btbl G1 H0 => btbl_schema d btbl = G1)
          (fun G0 Q0 H0 => exists s0, q_schema d Q0 true = s0)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF).
  Unshelve.
  + intros s0 c b btm btb G0 G1 Hbtb IHbtb Hc IHc Html. simpl. intro. rewrite e. reflexivity.
  + intros G0 btbl G1 c s0 b Hbtbl IHbtbl Hc IHc e Html. simpl.
    simpl in IHbtbl. unfold btbl_schema, btb_schema in IHbtbl.
    rewrite e. rewrite <- IHbtbl. reflexivity.
  + intros G0 b Q1 Q2 s0 s1 Hlen HQ1 IHQ1 HQ2 IHQ2; simpl; simpl in IHQ1; exact IHQ1.
  + intros G0 b Q1 Q2 s0 s1 Hlen HQ1 IHQ1 HQ2 IHQ2; simpl; simpl in IHQ1; exact IHQ1.
  + intros G0 b Q1 Q2 s0 s1 Hlen HQ1 IHQ1 HQ2 IHQ2; simpl; simpl in IHQ1; exact IHQ1.
  + intros x s0 G0 Hdb e. simpl. constructor.
  + intros x s0 G0 Hdb e. simpl. constructor.
  + intros G0 Hdb. reflexivity.
  + intros G0 Hdb. reflexivity.
  + intros G0 t b Hdb Ht. reflexivity.
  + intros; constructor.
  + intros; constructor.
  + intros; constructor.
  + intros; constructor.
  + intros; constructor.
  + intros; constructor.
  + intros; constructor.
  + intros; constructor.
  + intros G0 T s0 s' btb G1 Hlen Hnodup HT IHT Hbtb IHbtb. simpl. unfold btb_schema.
    simpl in IHbtb. unfold btb_schema, ret in IHbtb.
    rewrite IHbtb. reflexivity.
  + intros; reflexivity.
  + intros G1 btb btbl G2 G3 Hbtbl IHbtbl Hbtb IHbtb. simpl.
    simpl in IHbtbl, IHbtb. rewrite <- IHbtbl, <- IHbtb. reflexivity.
  + intros c b btm btb G0 G1 Hbtb IHbtb Hc IHc Html. simpl. eexists. all:auto.
  + intros G0 btb G1 c b Hbtb IHbtb Hc IHc. simpl. eexists. all:eauto.
  + intros G0 b Q1 Q2 s0 s1 Hlen HQ1 IHQ1 HQ2 IHQ2; simpl. rewrite IHQ1. exists s0; auto.
  + intros G0 b Q1 Q2 s0 s1 Hlen HQ1 IHQ1 HQ2 IHQ2; simpl. rewrite IHQ1. exists s0; auto.
  + intros G0 b Q1 Q2 s0 s1 Hlen HQ1 IHQ1 HQ2 IHQ2; simpl. rewrite IHQ1. exists s0; auto.
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