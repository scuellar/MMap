
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
        if X.eq_dec x y then (y, v) :: l else (y, v') :: add x v l
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

  Definition mapi {A A'} (f : key -> A -> A') : t A -> t A' :=
    List.map (fun p => (fst p, f (fst p) (snd p))).

  Definition map {A A'} (f : A -> A') : t A -> t A' :=
    mapi (fun k v => f v).

  Definition map2 {A A' A''} (f : option A -> option A' -> option A'') : t A -> t A' ->  t A''.
  Admitted.

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
    * inversion HM.
     - left; split. assumption. reflexivity.
     - right; assumption.
    * inversion HM.
      - inversion H. rewrite H1. constructor. assumption.
      - constructor. assumption.
  Qed.


  Lemma MapsTo_other: forall x k v v' l,
    ~ X.eq x k -> (MapsToA x v ((k,v') :: l) <-> MapsToA x v l).
  Proof.
    intros. rewrite MapsTo_cons. intuition.
  Qed.

  Definition MapsTo := MapsToA.

  Definition In (k:key)(m: t A) : Prop := exists e:A, MapsTo k e m.

  Lemma In_cons: forall x k v l,
    (In x ((k,v) :: l) <-> (X.eq x k) \/ In x l).
  Proof.
    intros.
    unfold In.
    split; intro H; inversion H.
     * rewrite MapsTo_cons in H0. inversion H0. left. intuition. right. exists x0. assumption.
     * exists v. constructor. assumption.
     * inversion H0. exists x0. constructor. assumption.
  Qed.    

  Lemma In_ind :
    forall (P : key -> t A -> Prop), 
    (forall k k' v m, X.eq k k' -> P k ((k',v)::m)) ->
    (forall k k' v m, P  k m -> P k ((k',v)::m)) ->
    forall k m, (In k m -> P k m).
  Proof.
    intros.
    unfold In in H1.
    inversion_clear H1.
    induction H2.
    - apply H; assumption.
    - apply H0; assumption.
  Qed.

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


  Instance MapsTo_compat : Proper (X.eq==>eq==>eq==>iff) MapsTo.
  Proof.
    repeat red; intros. subst. unfold MapsTo.
    split.
    * intro H1. induction H1.
      - constructor. transitivity x. symmetry. assumption. assumption.
      - constructor. assumption.
    * intro H1. induction H1. constructor. 
      - transitivity y. assumption. assumption.
      - constructor. assumption. 
  Qed.
  Hint Resolve MapsTo_compat.

  Instance In_compat : Proper (X.eq==>eq==>iff) In.
  Proof. unfold In.  solve_proper. Qed.
  Hint Resolve In_compat.

  Lemma mem_spec : forall s x `{Ok s}, mem x s = true <-> In x s.
  Proof.
    intros. split.
     - intro. induction s.
       + inversion H0.
       + destruct a.
         simpl in H0.
         destruct (X.eq_dec x k).
          * exists a. constructor. assumption.
          * assert (In x s).
              apply IHs. unfold Ok. inversion H. assumption. assumption.
            inversion H1. exists x0. constructor. assumption.
     - intro.
       induction H0.
       induction H0.
       + simpl. destruct (X.eq_dec x k).
         * reflexivity.
         * apply n in H0. inversion H0.
       + simpl. destruct (X.eq_dec x k).
         * reflexivity.
         * apply IHMapsToA. unfold Ok. inversion H. assumption.
  Qed.

  Lemma isok_iff : forall l, Ok l <-> isok l = true.
  Proof.
    intros.
    induction l as [ | (k,v) l ].
    - simpl. intuition. constructor.
    - simpl.
      rewrite andb_true_iff, negb_true_iff.
      rewrite <- IHl.
      split.
      + intro. inversion H. split.
        * apply not_true_is_false.
          assert (Ok l). unfold Ok. assumption.
          rewrite <- mem_spec in H2. assumption. assumption.
        * assumption.
      + intro. inversion H.
        constructor. intro contr.
        rewrite <- mem_spec in contr.
        rewrite H0 in contr. inversion contr.
        assumption.
        unfold Ok in H1. assumption.
  Qed.

  Global Instance isok_Ok l : isok l = true -> Ok l | 10.
  Proof.
    intro P. apply isok_iff. exact P.
  Qed.

  Lemma add_spec1: forall s k k' v `{Ok s},
     X.eq k k' -> MapsTo k v (add k' v s).
  Proof.
    intros.
    induction H.
    - constructor; assumption.
    - simpl.
      destruct (X.eq_dec k' x).
      + apply MapsTo_cons_hd. transitivity k'; assumption.
      + apply MapsTo_cons_tl. assumption.
  Qed.
  
  Lemma add_spec2: forall s k k' v v' `{Ok s},
     ~ X.eq k k' -> (MapsTo k v (add k' v' s) <-> MapsTo k v s).
  Proof.
    intros. 
    induction H.
    - simpl. rewrite MapsTo_other. apply iff_refl. assumption.
    - simpl. destruct (X.eq_dec k' x).
      + assert (~ X.eq k x).
          intro contr. apply H0. transitivity x. assumption. symmetry. assumption.
        repeat (rewrite MapsTo_cons). intuition.
      + repeat (rewrite MapsTo_cons). intuition.
  Qed.

  Lemma add_spec2_in: forall s k k' v `{Ok s},
     ~ X.eq k k' -> (In k (add k' v s) <-> In k s).
  Proof.
    intros. unfold In.
    split; intro HM; inversion HM. 
    - rewrite add_spec2 in H1. exists x. assumption. assumption. assumption.
    - exists x. rewrite add_spec2.  assumption. assumption. assumption.
  Qed.
                 
  Global Instance add_ok s k v `(Ok s) : Ok (add k v s).
  Proof.
    induction H.
    - constructor. intro H. inversion H. inversion H0. constructor.
    - simpl. destruct (X.eq_dec k x).
      + constructor; try assumption.
      + constructor. rewrite add_spec2_in; intuition.
        assumption.
  Qed.

  Lemma remove_noop: forall s k,
    ~ In k s -> remove k s = s.
  Proof.
    intros.
    induction s as [ | (x,v) s].
    - reflexivity.
    - assert (~ In k s). intro contr. apply H. rewrite In_cons. right. assumption.
      apply IHs in H0.
      simpl.
      rewrite In_cons in H.
      rewrite H0.
      destruct (X.eq_dec k x). intuition. reflexivity.
  Qed.

  Lemma remove_spec1: forall s k k' `{Ok s},
    X.eq k k' -> ~ In k (remove k' s).
  Proof.
    intros.
    induction H.
    - intro contr. inversion contr. inversion H.
    - intro contr. simpl in contr.
      destruct (X.eq_dec k' x).
      + rewrite H0 in contr. rewrite e in contr. apply H in contr. inversion contr.
      + rewrite In_cons in contr. intuition. apply n. rewrite <- H0. assumption.
  Qed.    

  Lemma remove_spec2: forall s k k' v `{Ok s},
    ~ X.eq k k' -> (MapsTo k' v (remove k s) <-> MapsTo k' v s).
  Proof.
    intros.
    induction H.
    - simpl. intuition.
    - simpl.
      destruct (X.eq_dec k x).
      + assert (~X.eq k' x). intro contr. apply H0. rewrite e. rewrite contr. intuition.
        rewrite MapsTo_cons. intuition.
      + repeat (rewrite MapsTo_cons). intuition.
  Qed.

  Lemma forall_iff_same: forall {X} (P P' : X -> Prop),
     (forall x, P x <-> P' x) -> ((exists x, P x) <-> (exists x, P' x)).
  Proof.
    intros X P P' Heq.
    split; intro H; inversion H.
    - rewrite Heq in H0. exists x. assumption.
    - rewrite <- Heq in H0. exists x. assumption.
  Qed.

  Lemma remove_spec2_In: forall s k k'`{Ok s},
    ~ X.eq k k' -> (In k' (remove k s) <-> In k' s).
  Proof.
    intros. unfold In. apply forall_iff_same. intro x. apply remove_spec2; assumption.
  Qed.

  Global Instance remove_ok s x `(Ok s) : Ok (remove x s).
  Proof.
    induction H.
    - constructor.
    - simpl. destruct (X.eq_dec x x0).
      + apply H0.
      + constructor.
        rewrite remove_spec2_In; assumption. 
        assumption.
  Qed.

  Lemma singleton_ok : forall k v, Ok (singleton k v).
  Proof.
    intros.
    unfold singleton, Ok. constructors. unfold In. intro.
    inversion H. inversion H0.
  Qed.

  Lemma singleton_spec : forall k k' v,
    X.eq k k' <-> MapsTo k v (singleton k' v).
  Proof.
    intros.
    split; intro H.
    - unfold singleton. rewrite MapsTo_cons. left. split. assumption. reflexivity.
    - inversion H. assumption. inversion H1.
  Qed.

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
    - intro; inv. unfold In in H. inversion H. inversion H0.
    - inversion H.
    - assert (In (fst p) (p :: s)).
        destruct p.  unfold In. exists a. constructor.
      auto.
      unfold In in H0. inversion H0. apply H in H1. inversion H1.
  Qed.

 
  Lemma elements_spec1 : forall s k v,
    InA eq_key_elt (k, v) (elements s) <-> MapsTo k v s.
  Proof.
    intros. unfold elements.
    induction s as [ | (k',v') s].
    - intuition. inversion H. inversion H.
    - intuition.
      inversion H1.
      + inversion H3. simpl in H5. simpl in H6. rewrite H6. constructor. assumption.
      + constructor. apply H. assumption.
      + inversion H1.
        * constructor. unfold eq_key_elt. simpl. split. assumption. reflexivity.
        * apply InA_cons_tl. apply H0. assumption.
  Qed.

  Lemma elements_spec2w : forall s `(Ok s),
     NoDupA eq_key (@elements A s).
  Proof.
    intros.
    unfold elements.
    induction H.
    - constructor.
    - constructor.
      intro contr. apply H.
      + clear H. clear H0. clear IHNoDup.
        induction contr as [ (k,v') l | (k,v') l].
        * unfold eq_key in H. simpl in H. rewrite In_cons. left. assumption.
        * rewrite In_cons. right. assumption.
      + assumption.
  Qed.


  Lemma fold_spec : forall s (X : Type) (i : X) (f : key -> A -> X -> X),
    fold f s i = fold_left (fun (x:X) (p:key*A) => f (fst p) (snd p) x ) (elements s) i.
    intros; reflexivity.
  Qed.

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
  Proof.
    intros.
    induction s as [|(k',v')].
    simpl.
    - split; intro H'; inversion H'; try inversion H0.
    - simpl.
      destruct (f k' v') eqn:Hf.
      + repeat (rewrite MapsTo_cons).
        intuition.
        rewrite <- H4 in Hf.
        rewrite <- H1 in Hf.
        assumption.
      + rewrite MapsTo_cons.
        rewrite IHs.
        intuition.
        rewrite <- H3 in Hf.
        rewrite <- H5 in Hf.
        rewrite Hf in H4.
        inversion H4.
  Qed.

  Lemma filter_In: forall f k l, ~ In k l -> ~ In k (filter f l).
  Proof.
    intros.
    induction l as [|(k',v')]; simpl.
    - apply H.
    - destruct (f k' v').
      + rewrite In_cons.
        rewrite In_cons in H.
        intuition.
      + rewrite In_cons in H.
        intuition.
  Qed.  
      
  Lemma filter_NoDup: forall f l, NoDup l -> NoDup (filter f l).
  Proof.
    intros.
    induction H.
    - constructor.
    - simpl.
      destruct (f x v).
      + constructor.
        * apply filter_In. assumption.
        * assumption.
      + assumption.
  Qed.
      
  Global Instance filter_ok s f `(Ok s) : Ok (filter f s).
  Proof.
    unfold Ok in H.
    induction H.
    - constructor.
    - simpl.
      destruct (f x v).
      + constructor.
        * apply filter_In. assumption.
        * apply filter_NoDup. assumption.
      + assumption.
  Qed.


  Lemma for_all_spec : forall s f,
    Proper (X.eq==>Logic.eq==>Logic.eq) f ->
    (for_all f s = true <-> For_all (fun x a => f x a = true) s).
  Proof.
    intros.
    unfold For_all.
    induction s as [|(k,v)].
    - simpl. split; intro.
      + intros k a contr. inversion contr.
      + reflexivity.
    - simpl.
      destruct (f k v) eqn:Hf.
      + split.
        * intros Hfa k0 a HMt.
          inversion HMt; subst; clear HMt.
          rewrite H1. assumption.
          apply IHs. assumption. assumption.
        * intros Hfa.
          apply IHs.
          intros k0 a HMt.
          apply Hfa.
          constructor. assumption.
      + split.
        * intro contr. inversion contr.
        * intro Hfa.
          assert (MapsTo k v ((k, v) :: s)) by ( constructor; reflexivity).
          specialize (Hfa k v H0).
          rewrite Hf in Hfa. assumption.
  Qed.
          
  Lemma exists_false_forall_true: forall A f (s : t A), 
   (exists_ f s = true <-> for_all (fun k v => negb (f k v)) s = false).
  Proof.
    intros.
    induction s as [|(k,v)].
    - simpl. intuition.
    - simpl. destruct (f k v); intuition.
  Qed.

  Lemma  exists_spec : forall s f ,
    Proper (X.eq==>Logic.eq==>Logic.eq) f ->
    (exists_ f s = true <-> Exists (fun x a => f x a = true) s).
  Proof.
    intros.
    unfold For_all.
    induction s as [|(k,v)].
    - simpl. split; intro.
      + inversion H0.
      + unfold Exists in H0. inversion H0. inversion H1. inversion H2. inversion H3.
    - simpl.
      destruct (f k v) eqn:Hf.
      + split.
        * intros.
          exists k. exists v.
          split ; [constructor;  reflexivity | assumption].
        * intro He. reflexivity.
      + split.
        * intros.
          apply IHs in H0.
          inversion H0. inversion_clear H1. inversion_clear H2.
          exists x. exists x0.
          split ; [constructor;  assumption | assumption].
        * intro He.
          inversion_clear He. inversion_clear H0. inversion_clear H1.
          inversion H0; subst; clear H0.
          rewrite H3 in H2. rewrite H2 in Hf. inversion Hf.
          apply IHs.
          exists x. exists x0.
          split ; assumption.
  Qed.

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


  Lemma choose_spec1 : forall s k v,
     choose s = Some (k,v) -> MapsTo k v s.
  Proof.
    intros.
    destruct s as [|(k',v')].
    - inversion H.
    - inversion H. constructor. reflexivity.
  Qed.

  Lemma choose_spec2 : forall s , choose s = None -> Empty s.
  Proof.
    intros.
    destruct s as [|(k',v')].
    - inversion H. apply empty_spec.
    - inversion H.
  Qed.


  (* Definition In := InA X.eq. *)
  Definition eq := Equal.
  Instance eq_equiv : Equivalence eq := _. Admitted.
  End ForNotations.


  Lemma map_spec1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
                      MapsTo x e m -> MapsTo x (f e) (map f m).
    intros. induction H; constructor; assumption.
  Qed.

  Lemma map_spec2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
                      In x (map f m) -> In x m.
    intros.
    remember (map f m) as m'.
    generalize dependent m.
    induction H using In_ind.
    - intros.
      destruct m0 as [|(k'',v') m0]; inversion Heqm'; subst; clear Heqm'.
      rewrite In_cons. left. assumption.
    - intros.
      destruct m0 as [|(k'',v'') m0]; inversion Heqm'; subst; clear Heqm'.
      rewrite In_cons. right. apply IHIn. reflexivity.
  Qed.
      
  Lemma mapi_spec1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
                        (f:key->elt->elt'), MapsTo x e m ->
                                            exists y, X.eq y x /\ MapsTo x (f y e) (mapi f m).
    intros.
    induction H.
    - exists k. split.
      + symmetry; assumption.
      + constructor; assumption.
    - inversion_clear IHMapsToA.
      inversion_clear H0.
      exists x0. split.
      + assumption.
      + constructor. assumption.
  Qed.



  Lemma mapi_spec2 : forall (elt elt':Type)(m: t elt)(x:key)
                            (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Proof.
    intros.
    remember (mapi f m) as m'.
    generalize dependent m.
    induction H using In_ind.
    - intros.
      destruct m0 as [|(k'',v') m0]; inversion Heqm'; subst; clear Heqm'.
      rewrite In_cons. left. assumption.
    - intros.
      destruct m0 as [|(k'',v'') m0]; inversion Heqm'; subst; clear Heqm'.
      rewrite In_cons. right. apply IHIn. reflexivity.
  Qed.

  Lemma map2_spec1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	                        (x:key)(f:option elt->option elt'->option elt''),
	                   In x m \/ In x m' ->
                       find x (map2 f m m') = f (find x m) (find x m').
  Admitted.

  Lemma map2_spec2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	                        (x:key)(f:option elt->option elt'->option elt''),
                       In x (map2 f m m') -> In x m \/ In x m'.
  Admitted.

  Instance mapi_ok A A' s (g: key -> A -> A') `(Ok A s): Ok (mapi g s).
  Proof.
    intros. induction H.
    - constructor.
    - simpl. constructor.
      + intro contr. apply H. clear H.
        apply mapi_spec2 in contr.
        unfold In in contr. assumption.
      + assumption.
  Qed.
 
  Instance map_ok A A' s (g: A -> A') `(Ok A s): Ok (map g s).
  Proof.
    unfold map.
    apply mapi_ok.
    assumption.
  Qed.

  Instance map2_ok A A' A'' s s' 
          (g: option A -> option A' -> option A'') `(Ok A s): Ok (map2 g s s').
  Admitted.
End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of lists without redundancy. *)

Module Make (X: DecidableType) <: WMaps with Module E := X.
 Module Raw := MakeRaw X.
 Include WRaw2Maps X Raw.
End Make.
