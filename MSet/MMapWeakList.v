(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite sets library *)

(** This file proposes an implementation of the non-dependant
    interface [MSetWeakInterface.S] using lists without redundancy. *)

Require Import MMapInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Functions over lists

   First, we provide sets as lists which are (morally) without redundancy.
   The specs are proved under the additional condition of no redundancy.
   And the functions returning sets are proved to preserve this invariant. *)


(** ** The set operations. *)

Module Ops (X: DecidableType) <: WOps X.

  Definition key := X.t.

  Section Foo.
  Variable A : Type.

  Definition t  := list (key * A).

  Definition empty : t := nil.

  Definition is_empty (l : t) : bool := if l then true else false.

  Fixpoint mem (x : key) (s : t) : bool :=
    match s with
    | nil => false
    | (k, v) :: l =>
           if X.eq_dec x k then true else mem x l
    end.

  Fixpoint find (x : key) (s : t) : option A :=
    match s with
    | nil => None
    | (k, v) :: l =>
           if X.eq_dec x k then Some v else find x l
    end.

  Fixpoint add (x : key) (v : A) (s : t) : t :=
    match s with
    | nil => (x, v) :: nil
    | (y, v') :: l =>
        if X.eq_dec x y then (y, v) :: s else (y, v') :: add x v l
    end.

  Definition singleton (x : key) (v : A) : t := (x, v) :: nil.

  Fixpoint remove (x : key) (s : t) : t :=
    match s with
    | nil => nil
    | (y, v) :: l =>
        if X.eq_dec x y then l else (y, v) :: remove x l
    end.

  Definition fold (B : Type) (f : key -> A -> B -> B) (s : t) (i : B) : B :=
    fold_left (fun a p => f (fst p) (snd p) a) s i.

  (*
  Definition union (s : t) : t -> t := fold add s.

  Definition diff (s s' : t) : t := fold (fun k v => remove k) s' s.

  Definition inter (s s': t) : t :=
    fold (fun x k s => if mem x s' then add x k s else s) s nil.
   *)
 
  Fixpoint filter (f : key -> A -> bool) (s : t) : t :=
    match s with
    | nil => nil
    | (x, v) :: l => if f x v then (x, v) :: filter f l else filter f l
    end.

  Fixpoint for_all (f : key -> A -> bool) (s : t) : bool :=
    match s with
    | nil => true
    | (x, v) :: l => if f x v then for_all f l else false
    end.

  Section ElemEq.
  Variable eq : A -> A -> bool.

  Definition subset (s s' : t) : bool :=
    for_all (fun k v =>
               match find k s' with
               | Some v' => eq v v'
               | None => false end) s.

  Definition equal (s s' : t) : bool := andb (subset s s') (subset s' s).
  End ElemEq.

  Fixpoint exists_ (f : key -> A -> bool) (s : t) : bool :=
    match s with
    | nil => false
    | (x, v) :: l => if f x v then true else exists_ f l
    end.

  Fixpoint partition (f : key -> A -> bool) (s : t) : t * t :=
    match s with
    | nil => (nil, nil)
    | (x, v) :: l =>
        let (s1, s2) := partition f l in
        if f x v then ((x,v) :: s1, s2) else (s1, (x,v) :: s2)
    end.

  Definition cardinal (s : t) : nat := length s.

  Definition elements (s : t) : list (key * A) := s.

  Definition choose (s : t) : option (key * A) :=
     match s with
      | nil => None
      | x::_ => Some x
     end.
  End Foo.
End Ops.

(** ** Proofs of set operation specifications. *)

Module MakeRaw (X:DecidableType) <: WRawMaps X.
  Include Ops X.

  Section ForNotations.
  Variable A : Type.

  Inductive MapsToA (x : key) (v : A) : t A -> Prop :=
  | MapsTo_cons_hd : forall k l, X.eq x k -> MapsToA x v ((k,v) :: l)
  | MapsTo_cons_tl : forall k v' l, MapsToA x v l -> MapsToA x v ((k,v') :: l).

  Lemma MapsTo_cons: forall x k v v' l,
    (MapsToA x v ((k,v') :: l) <-> (X.eq x k /\ v = v') \/ MapsToA x v l).
  Proof.
   intros. split; intro HM.
   inversion HM. left; split. assumption. reflexivity.
                 right; assumption.
   inversion HM. inversion H. rewrite H1. constructor. assumption.
                 constructor. assumption.
  Qed.


  Lemma MapsTo_other: forall x k v v' l,
    ~ X.eq x k -> (MapsToA x v ((k,v') :: l) <-> MapsToA x v l).
  Proof.
    intros. rewrite MapsTo_cons. intuition.
  Qed.

  Definition MapsTo := MapsToA.

  Definition In (k:key)(m: t A) : Prop := exists e:A, MapsTo k e m.
  Definition Empty m := forall k a, ~ MapsTo k a m.

  Definition eq_key (p p':key*A) := X.eq (fst p) (fst p').
  Definition eq_key_elt (p p':key*A) :=
          X.eq (fst p) (fst p') /\ (snd p) = (snd p').


  (* TODO: Copy explanation from FMap *)
  Definition Equal m m' := forall k, @find A k m = find k m'.
  Definition Equiv (eq_elt: A -> A -> Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
  Definition Equivb (cmp: A -> A -> bool) := Equiv (Cmp cmp).

  Definition For_all (P : key -> A -> Prop) m := forall k a, MapsTo k a m -> P k a.
  Definition Exists (P : key -> A -> Prop) m := exists k a, MapsTo k a m /\ P k a.


  Inductive NoDup : t A -> Prop :=
  | NoDup_nil : NoDup nil
  | NoDup_cons : forall x v l, ~ In x l -> NoDup l -> NoDup ((x,v)::l).

  (* TODO: modify proofs in order to avoid these hints *)
  Let eqr:= (@Equivalence_Reflexive _ _ X.eq_equiv).
  Let eqsym:= (@Equivalence_Symmetric _ _ X.eq_equiv).
  Let eqtrans:= (@Equivalence_Transitive _ _ X.eq_equiv).
  Hint Resolve eqr eqtrans.
  Hint Immediate eqsym.

  Definition IsOk := NoDup.

  Class Ok (s:t A) : Prop := ok : NoDup s.

  Hint Unfold Ok.
  Hint Resolve ok.

  Instance NoDup_Ok s (nd : NoDup s) : Ok s := { ok := nd }.

  Ltac inv_ok := match goal with
   | H:Ok (_ :: _) |- _ => inversion_clear H; inv_ok
   | H:Ok nil |- _ => clear H; inv_ok
   | H:NoDup ?l |- _ => change (Ok l) in H; inv_ok
   | _ => idtac
  end.

  Ltac inv := invlist InA; inv_ok.
  Ltac constructors := repeat constructor.

  Fixpoint isok l := match l with
   | nil => true
   | (x,v)::l => negb (@mem A x l) && isok l
  end.


  Lemma MapsTo_compat : Proper (X.eq==>eq==>eq==>iff) MapsTo.
  Proof.
  repeat red; intros. subst. unfold MapsTo.
  split.
  intro H1. induction H1. constructor.
  transitivity x. symmetry. assumption. assumption.
  constructor. assumption.

  intro H1. induction H1. constructor. 
  transitivity y. assumption. assumption.
  constructor. assumption. 
  Qed.

  Lemma mem_spec : forall s x `{Ok s},
   mem x s = true <-> In x s.
  Proof.
  intros.
  split.
  intro.
  induction s.
  inversion H0.
  destruct a.
  simpl in H0.
  destruct (X.eq_dec x k).
  exists a. constructor. assumption.
  assert (In x s).
    apply IHs. unfold Ok. inversion H. assumption. assumption.
  inversion H1. exists x0. constructor. assumption.

  intro.
  induction H0.
  induction H0.
  simpl.
  destruct (X.eq_dec x k). reflexivity. apply n in H0. inversion H0.
  simpl.
  destruct (X.eq_dec x k). reflexivity. apply IHMapsToA. unfold Ok. inversion H. assumption.
  Qed.


  Lemma isok_iff : forall l, Ok l <-> isok l = true.
  Proof.
    intros.
    induction l.
    simpl. intuition. constructor.
   
    destruct a.
    simpl.
    rewrite andb_true_iff, negb_true_iff.
    rewrite <- IHl.
    split.
    intro. inversion H. split.
      apply not_true_is_false.
      assert (Ok l). unfold Ok. assumption.
      rewrite <- mem_spec in H2. assumption. assumption. assumption.

    intro. inversion H. constructor.
      intro contr.
      rewrite <- mem_spec in contr.
      rewrite H0 in contr. inversion contr.
      assumption.
      unfold Ok in H1. assumption.
   Qed.

  Global Instance isok_Ok l : isok l = true -> Ok l | 10.
  Proof.
  intros. apply <- isok_iff; auto.
  Qed.


  Lemma add_spec1: forall s k k' v `{Ok s},
     X.eq k k' -> MapsTo k v (add k' v s).
   Proof.
    intros.
    induction H.
    constructor; assumption.
    simpl.
    destruct (X.eq_dec k' x).
    apply MapsTo_cons_hd. transitivity k'; assumption.
    apply MapsTo_cons_tl. assumption.
  Qed.
  
  Lemma add_spec2: forall s k k' v v' `{Ok s},
     ~ X.eq k k' -> (MapsTo k v (add k' v' s) <-> MapsTo k v s).
  Proof.
    intros. 
    induction H.
    simpl. rewrite MapsTo_other. apply iff_refl. assumption.
 
    simpl. destruct (X.eq_dec k' x).
    assert (~ X.eq k x).
      intro contr. apply H0. transitivity x. assumption. symmetry. assumption.
    repeat (rewrite MapsTo_cons). intuition.
    repeat (rewrite MapsTo_cons). intuition.
  Qed.

  (*
  Lemma add_spec :
   forall (s : t A) (x y : key) {Hs : Ok s},
     In y (add x s) <-> X.eq y x \/ In y s.
  Proof.
  induction s; simpl; intros.
  intuition; inv; auto.
  destruct X.eq_dec; inv; rewrite InA_cons, ?IHs; intuition.
  left; eauto.
  inv; auto.
  Qed.
  *)

  Global Instance add_ok s k v `(Ok s) : Ok (add k v s).
  (*
  Proof.
  induction s.
  simpl; intuition.
  intros; inv. simpl.
  destruct X.eq_dec; auto.
  constructors; auto.
  intro; inv; auto.
  rewrite add_spec in *; intuition.
  Qed.
  *)
  Admitted.


  Lemma remove_spec1: forall s k k' `{Ok s},
    X.eq k k' -> ~ In k (remove k' s).
   Admitted.

  Lemma remove_spec2: forall s k k' v `{Ok s},
    ~ X.eq k k' -> MapsTo k' v (remove k s) <-> MapsTo k' v s.
   Admitted.
  (*
  Lemma remove_spec :
   forall (s : t A) (x y : key) {Hs : Ok s},
     In y (remove x s) <-> In y s /\ ~X.eq y x.
  Proof.
  induction s; simpl; intros.
  intuition; inv; auto.
  destruct X.eq_dec; inv; rewrite !InA_cons, ?IHs; intuition.
  elim H. setoid_replace a with y; eauto.
  elim H3. setoid_replace x with y; eauto.
  elim n. eauto.
  Qed.
  *)

  Global Instance remove_ok s x `(Ok s) : Ok (remove x s).
  Admitted.
  (*
  Proof.
  induction s; simpl; intros.
  auto.
  destruct X.eq_dec; inv; auto.
  constructors; auto.
  rewrite remove_spec; intuition.
  Qed.
  *)

  Lemma singleton_ok : forall k v, Ok (singleton k v).
  Proof.
  intros.
  unfold singleton, Ok. constructors. unfold In. intro.
  inversion H. inversion H0.
  Qed.

  Lemma singleton_spec : forall k k' v,
    X.eq k k' <-> MapsTo k v (singleton k' v).
  Admitted.


  (*
  Lemma singleton_spec : forall x y : elt, In y (singleton x) <-> X.eq y x.
  Proof.
  unfold singleton; simpl; split; intros. inv; auto. left; auto.
  Qed.
  *)

  Lemma empty_ok : Ok (empty A).
  Proof.
  unfold empty; constructors.
  Qed.

  Lemma empty_spec : Empty (empty A).
  Proof.
  unfold Empty, empty; red; intros; inv.
  unfold In in H. inversion H.
  Qed.

  Lemma is_empty_spec : forall s : t A, is_empty s = true <-> Empty s.
  Proof.
  unfold Empty; destruct s; simpl; split; intros; auto.
  intro; inv. unfold In in H. inversion H. inversion H0. inversion H.
  assert (In (fst p) (p :: s)).
    destruct p.  unfold In. exists a. constructor.
    auto.
  unfold In in H0. inversion H0. apply H in H1. inversion H1.
  Qed.

  (*
  Lemma elements_spec1 : forall (s : t) (x : elt), In x (elements s) <-> In x s.
  Proof.
  unfold elements; intuition.
  Qed.

  Lemma elements_spec2w : forall (s : t) {Hs : Ok s}, NoDup (elements s).
  Proof.
  unfold elements; auto.
  Qed.
  *)

  Lemma fold_spec : forall s (X : Type) (i : X) (f : key -> A -> X -> X),
    fold f s i = fold_left (fun (x:X) (p:key*A) => f (fst p) (snd p) x ) (elements s) i.
  Admitted.                          

  (*
  Lemma fold_spec :
   forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (flip f) (elements s) i.
  Proof.
  reflexivity.
  Qed.

  Global Instance union_ok : forall s s' `(Ok s, Ok s'), Ok (union s s').
  Proof.
  induction s; simpl; auto; intros; inv; unfold flip; auto with *.
  Qed.

  Lemma union_spec :
   forall (s s' : t) (x : elt) {Hs : Ok s} {Hs' : Ok s'},
   In x (union s s') <-> In x s \/ In x s'.
  Proof.
  induction s; simpl in *; unfold flip; intros; auto; inv.
  intuition; inv.
  rewrite IHs, add_spec, InA_cons; intuition.
  Qed.

  Global Instance inter_ok s s' `(Ok s, Ok s') : Ok (inter s s').
  Proof.
  unfold inter, fold, flip.
  set (acc := nil (A:=elt)).
  assert (Hacc : Ok acc) by constructors.
  clearbody acc; revert acc Hacc.
  induction s; simpl; auto; intros. inv.
  apply IHs; auto.
  destruct (mem a s'); auto with *.
  Qed.

  Lemma inter_spec  :
   forall (s s' : t) (x : elt) {Hs : Ok s} {Hs' : Ok s'},
   In x (inter s s') <-> In x s /\ In x s'.
  Proof.
  unfold inter, fold, flip; intros.
  set (acc := nil (A:=elt)) in *.
  assert (Hacc : Ok acc) by constructors.
  assert (IFF : (In x s /\ In x s') <-> (In x s /\ In x s') \/ In x acc).
   intuition; unfold acc in *; inv.
  rewrite IFF; clear IFF. clearbody acc.
  revert acc Hacc x s' Hs Hs'.
  induction s; simpl; intros.
  intuition; inv.
  inv.
  case_eq (mem a s'); intros Hm.
  rewrite IHs, add_spec, InA_cons; intuition.
  rewrite mem_spec in Hm; auto.
  left; split; auto. rewrite H1; auto.
  rewrite IHs, InA_cons; intuition.
  rewrite H2, <- mem_spec in H3; auto. congruence.
  Qed.

  Global Instance diff_ok : forall s s' `(Ok s, Ok s'), Ok (diff s s').
  Proof.
  unfold diff; intros s s'; revert s.
  induction s'; simpl; unfold flip; auto; intros. inv; auto with *.
  Qed.

  Lemma diff_spec  :
   forall (s s' : t) (x : elt) {Hs : Ok s} {Hs' : Ok s'},
   In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
  unfold diff; intros s s'; revert s.
  induction s'; simpl; unfold flip.
  intuition; inv.
  intros. inv.
  rewrite IHs', remove_spec, InA_cons; intuition.
  Qed.

  Lemma subset_spec :
   forall (s s' : t) {Hs : Ok s} {Hs' : Ok s'},
   subset s s' = true <-> Subset s s'.
  Proof.
  unfold subset, Subset; intros.
  rewrite is_empty_spec.
  unfold Empty; intros.
  intuition.
  specialize (H a). rewrite diff_spec in H; intuition.
  rewrite <- (mem_spec a) in H |- *. destruct (mem a s'); intuition.
  rewrite diff_spec in H0; intuition.
  Qed.

  *)

 Section EqSpec.
     Variable s s' : t A.
     Variable cmp : A -> A -> bool.
     Lemma equal_1 : 
       forall `{Ok s, Ok s'},
       Equivb cmp s s' -> equal cmp s s' = true.
     Admitted.
     Lemma equal_2 :
       forall `{Ok s, Ok s'},
       equal cmp s s' = true -> Equivb cmp s s'.
     Admitted.
  End EqSpec. 

  (*

  Lemma equal_spec :
   forall (s s' : t) {Hs : Ok s} {Hs' : Ok s'},
   equal s s' = true <-> Equal s s'.
  Proof.
  unfold Equal, equal; intros.
  rewrite andb_true_iff, !subset_spec.
  unfold Subset; intuition. rewrite <- H; auto. rewrite H; auto.
  Qed.

  Definition choose_spec1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
  destruct s; simpl; intros; inversion H; auto.
  Qed.

  Definition choose_spec2 : forall s : t, choose s = None -> Empty s.
  Proof.
  destruct s; simpl; intros.
  intros x H0; inversion H0.
  inversion H.
  Qed.
  *)
 
  Lemma cardinal_spec : forall s `{Ok s}, cardinal s = length (elements s).
  Proof. auto. Qed.

  (*
  Lemma filter_spec' : forall s x f,
   In x (filter f s) -> In x s.
  Proof.
  induction s; simpl.
  intuition; inv.
  intros; destruct (f a); inv; intuition; right; eauto.
  Qed.
  *)

  Lemma filter_spec : forall s k v f,
    Proper (X.eq==>Logic.eq==>Logic.eq) f ->
    (MapsTo k v (filter f s) <-> MapsTo k v s /\ f k v = true).
  Admitted.

  (*
  Lemma filter_spec :
   forall (s : t) (x : elt) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
  induction s; simpl.
  intuition; inv.
  intros.
  destruct (f a) eqn:E; rewrite ?InA_cons, IHs; intuition.
  setoid_replace x with a; auto.
  setoid_replace a with x in E; auto. congruence.
  Qed.
  *)

  Global Instance filter_ok s f `(Ok s) : Ok (filter f s).
  Admitted.
  (*
  Proof.
  induction s; simpl.
  auto.
  intros; inv.
  case (f a); auto.
  constructors; auto.
  contradict H0.
  eapply filter_spec'; eauto.
  Qed.
  *)

  Lemma for_all_spec : forall s f,
    Proper (X.eq==>Logic.eq==>Logic.eq) f ->
    (for_all f s = true <-> For_all (fun x a => f x a = true) s).
  Admitted.

  (*
  Lemma for_all_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof.
  unfold For_all; induction s; simpl.
  intuition. inv.
  intros; inv.
  destruct (f a) eqn:F.
  rewrite IHs; intuition. inv; auto.
  setoid_replace x with a; auto.
  split; intros H'; try discriminate.
  intros.
  rewrite <- F, <- (H' a); auto.
  Qed.
  *)

  Lemma  exists_spec : forall s f ,
    Proper (X.eq==>Logic.eq==>Logic.eq) f ->
    (exists_ f s = true <-> Exists (fun x a => f x a = true) s).
  Admitted.

  (*
  Lemma exists_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof.
  unfold Exists; induction s; simpl.
  split; [discriminate| intros (x & Hx & _); inv].
  intros.
  destruct (f a) eqn:F.
  split; auto.
  exists a; auto.
  rewrite IHs; firstorder.
  inv.
  setoid_replace a with x in F; auto; congruence.
  exists x; auto.
  Qed.
  *)

  Lemma partition_spec1 : forall s f,
    Proper (X.eq==>Logic.eq==>Logic.eq) f ->
    Equal (fst (partition f s)) (filter f s).
  Admitted.

  (*
  Lemma partition_spec1 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   Equal (fst (partition f s)) (filter f s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  firstorder.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl; intros.
  case (f x); simpl; firstorder; inversion H0; intros; firstorder.
  Qed.
  *)

  Lemma partition_spec2 : forall s f,
    Proper (X.eq==>Logic.eq==>Logic.eq) f ->
    Equal (snd (partition f s)) (filter (fun x a => negb (f x a)) s).
  Admitted.

  (*
  Lemma partition_spec2 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  firstorder.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl; intros.
  case (f x); simpl; firstorder; inversion H0; intros; firstorder.
  Qed.
  *)
  
  (*
  Lemma partition_ok1' :
   forall (s : t) {Hs : Ok s} (f : elt -> bool)(x:elt),
    In x (fst (partition f s)) -> In x s.
  Proof.
  induction s; simpl; auto; intros. inv.
  generalize (IHs H1 f x).
  destruct (f a); destruct (partition f s); simpl in *; auto.
  inversion_clear H; auto.
  Qed.

  Lemma partition_ok2' :
   forall (s : t) {Hs : Ok s} (f : elt -> bool)(x:elt),
    In x (snd (partition f s)) -> In x s.
  Proof.
  induction s; simpl; auto; intros. inv.
  generalize (IHs H1 f x).
  destruct (f a); destruct (partition f s); simpl in *; auto.
  inversion_clear H; auto.
  Qed.
  *)

  Global Instance partition_ok1 : forall s f `(Ok s), Ok (fst (partition f s)).
  Admitted.
  (*
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (@partition_ok1' _ _ f x).
  generalize (Hrec f H0).
  case (f x); case (partition f l); simpl; constructors; auto.
  Qed.
  *)

  Global Instance partition_ok2 : forall s f `(Ok s), Ok (snd (partition f s)).
  Admitted.
(*
  Proof.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (@partition_ok2' _ _ f x).
  generalize (Hrec f H0).
  case (f x); case (partition f l); simpl; constructors; auto.
  Qed.
*)

  Lemma elements_spec1 : forall s k v,
    InA eq_key_elt (k, v) (elements s) <-> MapsTo k v s.
  Admitted.

  Lemma elements_spec2w : forall s,
     NoDupA eq_key (@elements A s).
  Admitted.

  Lemma choose_spec1 : forall s k v,
     choose s = Some (k,v) -> MapsTo k v s.
  Admitted.

  Lemma choose_spec2 : forall s , choose s = None -> Empty s.
  Admitted.



  (* Definition In := InA X.eq. *)
  Definition eq := Equal.
  Instance eq_equiv : Equivalence eq := _. Admitted.
  End ForNotations.
End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of lists without redundancy. *)

Module Make (X: DecidableType) <: WMaps with Module E := X.
 Module Raw := MakeRaw X.
 Include WRaw2Maps X Raw.
End Make.
