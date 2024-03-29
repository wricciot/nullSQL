Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Util.

Module Type REL.
  Parameter R : nat -> Type.
  Parameter V : Type.
  Definition T := Vector.t V.
  Parameter memb   : forall n, R n -> T n -> nat.
  Parameter plus  : forall n, R n -> R n -> R n.
  Parameter minus : forall n, R n -> R n -> R n.
  Parameter inter : forall n, R n -> R n -> R n.
  Parameter times : forall m n, R m -> R n -> R (m + n).
  Parameter sum   : forall m n, R m -> (T m -> T n) -> R n.
  Parameter rsum  : forall m n, R m -> (T m -> R n) -> R n.
  Parameter sel   : forall n, R n -> (T n -> bool) -> R n.
  Parameter flat  : forall n, R n -> R n.
  Parameter supp  : forall n, R n -> list (T n).

  Implicit Arguments memb [n].
  Implicit Arguments plus [n].
  Implicit Arguments minus [n].
  Implicit Arguments inter [n].
  Implicit Arguments times [m n].
  Implicit Arguments sum [m n].
  Implicit Arguments rsum [m n].
  Implicit Arguments sel [n].
  Implicit Arguments flat [n].
  Implicit Arguments supp [n].

  Definition card := fun n S => memb (@sum n 0 S (fun _ => Vector.nil _)) (Vector.nil _).
  Implicit Arguments card [n].

  Parameter Rnil : forall n, R n.
  Parameter Rone : R 0.
  Parameter Rsingle : forall n, T n -> R n.

  Implicit Arguments Rnil [n].
  Implicit Arguments Rsingle [n].

  (* generalized cartesian product of m relations, each taken with its arity n *)
  Fixpoint prod (Rl : list { n : nat & R n }) 
    : R (list_sum (List.map (projT1 (P := fun n => R n)) Rl)) :=
  match Rl as r return R (list_sum (List.map (projT1 (P := fun n => R n)) r)) with
  | List.nil => Rone
  | List.cons (existT _ x R) l0 => times R (prod l0)
  end.

  Hypothesis V_eqb : V -> V -> bool.
  Parameter T_eqb : forall n, T n -> T n -> bool.
  Implicit Arguments T_eqb [n].

  Definition flatnat := fun n => match n with 0 => 0 | _ => 1 end.

  Hypothesis V_dec : forall (v w : V), {v = w} + {v <> w}.
  Hypothesis V_eqb_eq : forall (v w : V), V_eqb v w = true <-> v = w.
  Parameter T_dec : forall n, forall (x y : T n), {x = y} + {x <> y}.

  Parameter T_eqb_eq : forall n, forall (v w : T n), T_eqb v w = true <-> v = w.

  Parameter p_fs : forall n, forall r : R n, forall t, memb r t > 0 -> List.In t (supp r).
  Parameter p_fs_r : forall n, forall r : R n, forall t, List.In t (supp r) -> memb r t > 0.
  Parameter p_nodup : forall n, forall r : R n, NoDup (supp r).
  Parameter p_plus : forall n, forall r1 r2 : R n, forall t, memb (plus r1 r2) t = memb r1 t + memb r2 t.
  Parameter p_minus : forall n, forall r1 r2 : R n, forall t, memb (minus r1 r2) t = memb r1 t - memb r2 t.
  Parameter p_inter : forall n, forall r1 r2 : R n, forall t, memb (inter r1 r2) t = min (memb r1 t) (memb r2 t).
  Parameter p_times : forall m n, forall r1 : R m, forall r2 : R n, forall t t1 t2, 
                      t = Vector.append t1 t2 -> memb (times r1 r2) t = memb r1 t1 * memb r2 t2.
  Parameter p_sum : forall m n, forall r : R m, forall f : T m -> T n, forall t, 
                    memb (sum r f) t = list_sum (List.map (memb r) (filter (fun x => T_eqb (f x) t) (supp r))).
  Parameter p_rsum : forall m n, forall r : R m, forall f : T m -> R n, forall t,
                    memb (rsum r f) t = list_sum (List.map (fun t0 => memb r t0 * memb (f t0) t) (supp r)).
  Parameter p_self : forall n, forall r : R n, forall p t, p t = false -> memb (sel r p) t = 0.
  Parameter p_selt : forall n, forall r : R n, forall p t, p t = true -> memb (sel r p) t = memb r t.
  Parameter p_flat : forall n, forall r : R n, forall t, memb (flat r) t = flatnat (memb r t).
  Parameter p_nil : forall n (t : T n), memb Rnil t = 0.
  Parameter p_one : forall t, memb Rone t = 1.
  Parameter p_single : forall n (t : T n), memb (Rsingle t) t = 1.
  Parameter p_single_neq : forall n (t1 t2 : T n), t1 <> t2 -> memb (Rsingle t1) t2 = 0.

  Parameter p_ext : forall n, forall r s : R n, (forall t, memb r t = memb s t) -> r = s.

End REL.