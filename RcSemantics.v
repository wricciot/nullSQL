Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat RcSyntax AbstractRelation Bool.Sumbool Tribool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Util Common Eval SemFacts.

Module RcSemantics (Sem: SEM) (Rc : RC).
  Import Db.
  Import Rc.
  Import Sem.
  Import Evl.
  Module SF := SemFacts.Facts.
  Import SF.

  Definition sem_empty : forall n, Rel.R n -> B :=
    fun n r => of_bool(Rel.card r =? 0).

  Definition sem_nil : forall n, Rel.R n.
    intro n.
    epose (r := Rel.Rsingle (cast _ _ _ (of_list (List.repeat None n)))).
    apply (Rel.sel r (fun _ => false)).
    Unshelve.
    rewrite repeat_length. reflexivity.
  Defined.

  Inductive j_base_sem (d : Db.D) : forall G (t :  tm), (env G -> Value) -> Prop :=
  | jbs_cst  : forall G c,
      j_base_sem d G (cst c) (fun _ => Db.c_sem c)
  | jbs_null : forall G, j_base_sem d G null (fun _ => None)
  | jbs_proj : forall G i a,
      forall Sia,
      j_fvar_sem G i a Sia -> j_base_sem d G (proj (var i) a) Sia.

  Inductive j_basel_sem (d : Db.D) : forall G (tml : list tm), (env G -> Rel.T (List.length tml)) -> Prop :=
  | jbls_nil  : forall G, j_basel_sem d G List.nil (fun _ => Vector.nil _)
  | jbls_cons : forall G t tml,
      forall St Stml,
      j_base_sem d G t St -> j_basel_sem d G tml Stml ->
      j_basel_sem d G (t::tml) (fun h => Vector.cons _ (St h) _ (Stml h)).

  Inductive j_tuple_sem (d : Db.D) : forall G (t:tm) (s:Scm), (env G -> Rel.T (List.length s)) -> Prop :=
  | jts_mktup : forall G al bl,
      forall e Sbl, List.NoDup al -> List.length al = List.length bl -> j_basel_sem d G bl Sbl ->
      j_tuple_sem d G (mktup (List.combine al bl)) al (cast _ _ e Sbl).

  Inductive j_cond_sem (d : Db.D) : forall G (t:tm), (env G -> B) -> Prop :=
  | jws_empty : forall G q b n, 
      forall Sq, j_coll_sem d G q b n Sq ->
      j_cond_sem d G (empty b q) (fun h => sem_empty _ (Sq h))
  | jws_pred : forall G n p tml,
     forall Stml e,
     j_basel_sem d G tml Stml ->
     j_cond_sem d G (pred n p tml) 
       (fun Vl => Sem.sem_bpred _ p (to_list (Stml Vl)) (eq_trans (length_to_list _ _ _) e))
  | jws_true : forall G, j_cond_sem d G rctrue (fun _ => Sem.btrue)
  | jws_false : forall G, j_cond_sem d G rcfalse (fun _ => Sem.bfalse)
  | jws_isnull : forall G t,
      forall St, j_base_sem d G t St ->
      j_cond_sem d G (isnull t) (fun Vl => Sem.of_bool (match St Vl with None => true | _ => false end))
  | jws_istrue : forall G c,
      forall Sc, j_cond_sem d G c Sc ->
      j_cond_sem d G (istrue c) (fun Vl => Sem.of_bool (Sem.is_btrue (Sc Vl)))
  | jws_and : forall G c1 c2,
      forall Sc1 Sc2, j_cond_sem d G c1 Sc1 -> j_cond_sem d G c2 Sc2 ->
      j_cond_sem d G (rcand c1 c2) (fun Vl => Sem.band (Sc1 Vl) (Sc2 Vl))
  | jws_or : forall G c1 c2,
      forall Sc1 Sc2, j_cond_sem d G c1 Sc1 -> j_cond_sem d G c2 Sc2 ->
      j_cond_sem d G (rcor c1 c2) (fun Vl => Sem.bor (Sc1 Vl) (Sc2 Vl))
  | jws_not : forall G c,
      forall Sc, j_cond_sem d G c Sc ->
      j_cond_sem d G (rcnot c) (fun Vl => Sem.bneg (Sc Vl))

  with j_coll_sem (d : Db.D) : forall G (t : tm) (b:bool) (s:Scm), (env G -> Rel.R (List.length s)) -> Prop :=
  | jcs_nnil : forall G b s,
     List.NoDup s -> j_coll_sem d G (nil b s) b s (fun h => sem_nil _)
  | jcs_ndisj : forall G t b s,
     forall St,
     j_disjunct_sem d G t b s St ->
     j_coll_sem d G t b s St
  | jcs_nunion : forall G t1 t2 b s,
      forall St1 St2,
      j_disjunct_sem d G t1 b s St1 ->
      j_coll_sem d G t2 b s St2 ->
      let S := fun h => if b then Rel.flat (Rel.plus (St1 h) (St2 h)) else Rel.plus (St1 h) (St2 h) in
      j_coll_sem d G (union t1 t2) b s S

  with j_disjunct_sem (d : Db.D) : forall G (t : tm) (b : bool) (s:Scm), (env G -> Rel.R (List.length s)) -> Prop :=
  | jds_single : forall G b tup c,
      forall stup Stup Sc, j_tuple_sem d G tup stup Stup -> j_cond_sem d G c Sc ->
      j_disjunct_sem d G (cwhere (single b tup) c) b stup 
        (fun h => if Sem.is_btrue (Sc h) then Rel.Rsingle (Stup h) else sem_nil _)
  | jds_comprn : forall G q1 q2,
      forall b sq2 Sq2 sq1 Sq1 e,
      j_gen_sem d G q2 b sq2 Sq2 ->
      j_disjunct_sem d (sq2::G) q1 b sq1 Sq1 ->
      j_disjunct_sem d G (comprn q1 q2) b sq1 (fun h =>
        let f := fun (Vl : Rel.T (length sq2)) => Sq1 (env_app _ _ (Evl.env_of_tuple (sq2::List.nil) (cast _ _ e Vl)) h) in
        let S := Rel.rsum (Sq2 h) f in
        if b then Rel.flat S else S)

  with j_gen_sem (d : Db.D) : forall G (t : tm) (b : bool) (s : Scm), (env G -> Rel.R (List.length s)) -> Prop :=
  | jgs_tab : forall G x,
      forall s (e : Db.db_schema d x = Some s),
      j_gen_sem d G (tab x) false _ (fun _ => Db.db_rel e)
  | jgs_prom : forall G q,
      forall s Sq,
      j_coll_sem d G q true s Sq ->
      j_gen_sem d G (prom q) false s Sq
  | jgs_bagdiff : forall G q1 q2,
      forall s Sq1 Sq2,
      j_coll_sem d G q1 false s Sq1 -> j_coll_sem d G q2 false s Sq2 ->
      j_gen_sem d G (diff q1 q2) false s (fun h => Rel.minus (Sq1 h) (Sq2 h))
  | jgs_dtab : forall G x,
      forall s (e : Db.db_schema d x = Some s),
      j_gen_sem d G (dist (tab x)) true s (fun _ => Rel.flat (Db.db_rel e))
  | jgs_ddiff : forall G q1 q2,
      forall s Sq1 Sq2,
      j_coll_sem d G q1 false s Sq1 -> j_coll_sem d G q2 false s Sq2 ->
      j_gen_sem d G (dist (diff q1 q2)) true s (fun h => Rel.flat (Rel.minus (Sq1 h) (Sq2 h))).

  Scheme jws_ind_mut   := Induction for j_cond_sem      Sort Prop
  with   jcs_ind_mut   := Induction for j_coll_sem      Sort Prop
  with   jds_ind_mut   := Induction for j_disjunct_sem  Sort Prop
  with   jgs_ind_mut   := Induction for j_gen_sem       Sort Prop.

  Combined Scheme j_sem_ind_mut from jws_ind_mut, jcs_ind_mut, jds_ind_mut, jgs_ind_mut.


End RcSemantics.