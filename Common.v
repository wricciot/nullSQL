Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat AbstractRelation Omega.


Fixpoint findpos {A} (l : list A) (p : A -> bool) start {struct l} : option nat := 
  match l with
  | List.nil => None
  | List.cons a l0 => if p a then Some start else findpos l0 p (S start)
  end.

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

Lemma findpos_Some A (s : list A) p :
  forall m n, findpos s p m = Some n -> n < m + length s.
Proof.
  elim s; simpl; intros; intuition.
  + discriminate H.
  + destruct (p a); intuition.
    - injection H0. omega. 
    - pose (H _ _ H0). omega.
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

