Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat AbstractRelation Tribool Common.

Module Type RC.
  Import Db.

  Inductive tm :=
  | cst    : BaseConst -> tm
  | null   : tm
  | pred   : forall n, (forall l : list BaseConst, length l = n -> bool) -> list tm -> tm
  | var    : nat -> tm
  | mktup  : list (Name * tm) -> tm
  | proj   : tm -> Name -> tm
  | tab    : Name -> tm
  | nil    : bool -> Scm -> tm      (* is set, schema *)
  | single : bool -> tm -> tm       (* is_set *)
  | union  : tm -> tm -> tm
  | inters : tm -> tm -> tm
  | diff   : tm -> tm -> tm
  | comprn : tm -> tm -> tm
  | cwhere : tm -> tm -> tm
  | dist   : tm -> tm
  | prom   : tm -> tm
  | empty  : bool -> tm -> tm
  .

  Inductive j_var (a : Name) : Scm -> Prop :=
  | j_varhd   : forall s, ~ List.In a s -> j_var a (a::s)
  | j_varcons : forall b s, a <> b -> j_var a s -> j_var a (b::s).

  Inductive j_base (d : Db.D) : list Scm -> tm -> Prop :=
  | j_cst  : forall g c, j_base d g (cst c)
  | j_null : forall g, j_base d g null
  | j_proj : forall g t x s, j_tuple d g t s -> j_var x s -> j_base d g (proj t x)

  with j_tuple (d : Db.D) : list Scm -> tm -> Scm -> Prop :=
  | j_tmvar : forall g n s, List.nth_error g n = Some s -> j_tuple d g (var n) s
  | j_mktup : forall g bl, 
      List.NoDup (List.map fst bl) ->
      (forall g t, List.In t (List.map snd bl) -> j_base d g t)
      -> j_tuple d g (mktup bl) (List.map fst bl).

  Inductive j_cond (d : Db.D) : list Scm -> tm -> Prop :=
  | j_empty : forall g q b s, j_coll d g q b s -> j_cond d g (empty b q)
  | j_pred : forall g n p tl, 
      (forall t, List.In t tl -> j_base d g t) -> length tl = n 
      -> j_cond d g (pred n p tl)

  with j_coll (d : Db.D) : list Scm -> tm -> bool -> Scm -> Prop :=
  | j_tab : forall g x s, Db.db_schema d x = Some s -> j_coll d g (tab x) false s
  | j_nil : forall g b s, j_coll d g (nil b s) b s
  | j_single : forall g b t s, j_tuple d g t s -> j_coll d g (single b t) b s
  | j_union : forall g q1 q2 b s, j_coll d g q1 b s -> j_coll d g q2 b s -> j_coll d g (union q1 q2) b s
  | j_inters : forall g q1 q2 b s , j_coll d g q1 b s -> j_coll d g q2 b s -> j_coll d g (inters q1 q2) b s
  | j_diff : forall g q1 q2 b s, j_coll d g q1 b s -> j_coll d g q2 b s -> j_coll d g (diff q1 q2) b s
  | j_comprn : forall g q1 q2 b s1 s2, j_coll d g q2 b s2 -> j_coll d (s2::g) q1 b s1 -> j_coll d g (comprn q1 q2) b s1
  | j_cwhere : forall g q s c b, j_coll d g q b s -> j_cond d g c -> j_coll d g (cwhere q c) b s
  | j_dist : forall g q s, j_coll d g q false s -> j_coll d g (dist q) true s
  | j_prom : forall g q s, j_coll d g q true s -> j_coll d g (prom q) false s.

  Fixpoint bigunion (b : bool) (s : Scm) (ql : list tm) : tm :=
    match ql with
    | List.nil => nil b s
    | q0::ql0 => union q0 (bigunion b s ql0)
    end.

  Fixpoint multi_comprn q ql : tm :=
    match ql with
    | List.nil => q
    | q0::ql0 => multi_comprn (comprn q q0) ql0
    end.

  Definition not_union t := 
    match t with
    | union _ _ => false
    | _ => true
    end.


  (* normal forms *)
  Inductive j_nbase (d : Db.D) : list Scm -> tm -> Prop :=
  | j_ncst  : forall g c, j_nbase d g (cst c)
  | j_nnull  : forall g, j_nbase d g null
  | j_nproj : forall g n x s, List.nth_error g n = Some s -> j_var x s -> j_nbase d g (proj (var n) x).

  Definition j_nbasel d g tl := forall t, List.In t tl -> j_nbase d g t.

  Inductive j_ntuple (d : Db.D) : list Scm -> tm -> Scm -> Prop :=
  | j_nmktup : forall g bl, 
      List.NoDup (List.map fst bl) -> j_nbasel d g (List.map snd bl)
      -> j_ntuple d g (mktup bl) (List.map fst bl).

  Inductive j_ncond (d : Db.D) : list Scm -> tm -> Prop :=
  | j_nempty : forall g q b s, j_ncoll d g q b s -> j_ncond d g (empty b q)
  | j_npred : forall g n p tl, 
      j_nbasel d g tl -> length tl = n
      -> j_ncond d g (pred n p tl)

  with j_ncoll (d : Db.D) : list Scm -> tm -> bool -> Scm -> Prop :=
  | j_ncnil : forall g b s, j_ncoll d g (nil b s) b s
  | j_ncdisjunct : forall g t b s, not_union t = true -> j_ndisjunct d g t b s -> j_ncoll d g t b s
  | j_ncunion : forall g t1 t2 b s, 
      j_ndisjunct d g t1 b s ->
      j_ncoll d g t2 b s
      -> j_ncoll d g (union t1 t2) b s

  with j_ndisjunct (d : Db.D) : list Scm -> tm -> bool -> Scm -> Prop :=
  | j_nsingle : forall g b tup c, 
      forall s, j_ntuple d g tup s -> j_ncond d g c
      -> j_ndisjunct d g (cwhere (single b tup) c) b s
  | j_ncomprn : forall g q1 q2,
      forall b s s2, j_ngen d g q2 b s2 -> j_ndisjunct d (s2::g) q1 b s
      -> j_ndisjunct d g (comprn q1 q2) b s

  with j_ngen (d : Db.D) : list Scm -> tm -> bool -> Scm -> Prop :=
  | j_ntab : forall g x s, Db.db_schema d x = Some s -> j_ngen d g (tab x) false s
  | j_nprom : forall g q s, j_ncoll d g q true s -> j_ngen d g (prom q) false s
  | j_nbagdiff : forall g q1 q2 s, 
      j_ncoll d g q1 false s -> j_ncoll d g q2 false s 
      -> j_ngen d g (diff q1 q2) false s
  | j_ndtab : forall g x s, Db.db_schema d x = Some s -> j_ngen d g (dist (tab x)) true s
  | j_nddiff : forall g q1 q2 s,
      j_ncoll d g q1 false s -> j_ncoll d g q2 false s
      -> j_ngen d g (dist (diff q1 q2)) true s
  .

  Scheme jnw_ind_mut := Induction for j_ncond      Sort Prop
  with jnc_ind_mut   := Induction for j_ncoll      Sort Prop
  with jnd_ind_mut   := Induction for j_ndisjunct  Sort Prop
  with jng_ind_mut   := Induction for j_ngen       Sort Prop.

  Combined Scheme j_norm_ind_mut from jnw_ind_mut, jnc_ind_mut, jnd_ind_mut, jng_ind_mut.


End RC.