(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Finite maps library *)

(** This file proposes an implementation of the non-dependant
    interface [MMapInterface.S] using strictly ordered list. *)

Require Export MMapInterface OrdersFacts OrdersLists.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Functions over lists

   First, we provide maps as lists which are not necessarily sorted.
   The specs are proved under the additional condition of being sorted.
   And the functions returning maps are proved to preserve this invariant. *)

Module Ops (X:OrderedType) <: WOps X.

  Section Foo.

  Variable A : Type.

  Definition key := X.t.
  Definition t A := list (key * A).

  Definition empty : t A := nil.

  Definition is_empty (l : t A) := if l then true else false.

  (** ** The maps operations. *)

  Fixpoint mem k (m : t A) :=
    match m with
    | nil => false
    | (k', _) :: l =>
        match X.compare k k' with
        | Lt => false
        | Eq => true
        | Gt => mem k l
        end
    end.

  Fixpoint find k (m : t A) :=
    match m with
    | nil => None
    | (k', v) :: l =>
        match X.compare k k' with
        | Lt => None
        | Eq => Some v
        | Gt => find k l
        end
    end.

  Fixpoint add k v (m : t A) :=
    match m with
    | nil => (k, v) :: nil
    | (k', v') :: l =>
        match X.compare k k' with
        | Lt => (k, v) :: m
        | Eq => (k, v) :: l
        | Gt => (k', v') :: add k v l
        end
    end.

  Definition singleton (k : key) (v : A) := (k, v) :: nil.

  Fixpoint remove k (m : t A) :=
    match m with
    | nil => nil
    | (k', v) :: l =>
        match X.compare k k' with
        | Lt => m
        | Eq => l
        | Gt => (k', v) :: remove k l
        end
    end.

(*
  Fixpoint union (m : t) : t -> t :=
    match m with
    | nil => fun m' => m'
    | x :: l =>
        (fix union_aux (m' : t) : t :=
           match m' with
           | nil => m
           | x' :: l' =>
               match X.compare x x' with
               | Lt => x :: union l m'
               | Eq => x :: union l l'
               | Gt => x' :: union_aux l'
               end
           end)
    end.

  Fixpoint inter (m : t) : t -> t :=
    match m with
    | nil => fun _ => nil
    | x :: l =>
        (fix inter_aux (m' : t) : t :=
           match m' with
           | nil => nil
           | x' :: l' =>
               match X.compare x x' with
               | Lt => inter l m'
               | Eq => x :: inter l l'
               | Gt => inter_aux l'
               end
           end)
    end.

  Fixpoint diff (m : t) : t -> t :=
    match m with
    | nil => fun _ => nil
    | x :: l =>
        (fix diff_aux (m' : t) : t :=
           match m' with
           | nil => m
           | x' :: l' =>
               match X.compare x x' with
               | Lt => x :: diff l m'
               | Eq => diff l l'
               | Gt => diff_aux l'
               end
           end)
    end.
*)
  Fixpoint equal (val_eq : A -> A -> bool) (m : t A) (m' : t A) : bool :=
    match m, m' with
    | nil, nil => true
    | (k, v) :: l, (k', v') :: l' =>
        match X.compare k k' with
        | Eq => val_eq v v' && equal val_eq l l'
        | _  => false
        end
    | _, _ => false
    end.

  Fixpoint subset (val_eq : A -> A -> bool) m m' :=
    match m, m' with
    | nil, _ => true
    | (k, v) :: l, (k', v') :: l' =>
        match X.compare k k' with
        | Lt => false
        | Eq => val_eq v v' && subset val_eq l l'
        | Gt => subset val_eq m l'
        end
    | _, _ => false
    end.

  Definition fold (B : Type) (f : key -> A -> B -> B) (m : t A) (i : B) : B :=
    fold_left (fun acc p => f (fst p) (snd p) acc) m i.

  Fixpoint filter (f : key -> A -> bool) (m : t A) : t A :=
    match m with
    | nil => nil
    | (k, v) :: l => if f k v then (k, v) :: filter f l else filter f l
    end.

  Fixpoint for_all (f : key -> A -> bool) (m : t A) : bool :=
    match m with
    | nil => true
    | (k, v) :: l => if f k v then for_all f l else false
    end.

  Fixpoint exists_ (f : key -> A -> bool) (m : t A) : bool :=
    match m with
    | nil => false
    | (k, v) :: l => if f k v then true else exists_ f l
    end.

  Fixpoint partition (f : key -> A -> bool) (m : t A) : t A * t A :=
    match m with
    | nil => (nil, nil)
    | (k, v) :: l =>
        let (s1, s2) := partition f l in
        if f k v then ((k, v) :: s1, s2) else (s1, (k, v) :: s2)
    end.

  Definition cardinal (m : t A) : nat := length m.

  Definition elements (m : t A) : list (key * A) := m.

  Definition min_key (m : t A) : option key :=
    match m with
    | nil => None
    | p :: _ => Some (fst p)
    end.

  Fixpoint max_key (m : t A) : option key :=
    match m with
    | nil => None
    | p :: nil => Some (fst p)
    | _ :: l => max_key l
    end.

  Definition choose (m : t A) := head m.

(*
  Fixpoint compare m m' :=
   match m, m' with
    | nil, nil => Eq
    | nil, _ => Lt
    | _, nil => Gt
    | x::m, x'::m' =>
      match X.compare x x' with
       | Eq => compare m m'
       | Lt => Lt
       | Gt => Gt
      end
   end.
*)
  End Foo.
End Ops.


Module MakeRaw (X: OrderedType) <: RawMaps X.

  Module Import MX := OrderedTypeFacts X.
  Module Import ML := OrderedTypeLists X.

  Include Ops X.

  (** ** Proofs of set operation specifications. *)

  Section ForNotations.
  Variable A : Type.

  Definition inf k (l : t A) :=
   match l with
   | nil => true
   | (k', v) :: _ => match X.compare k k' with Lt => true | _ => false end
   end.

  Fixpoint isok l :=
   match l with
   | nil => true
   | (k, v) :: l => inf k l && isok l
   end.

  Notation Sort l := (isok l = true).
  Notation Inf k l := (lelistA X.lt k (map (@fst X.t A) l)).
  Notation In := (InA X.eq).

  Existing Instance X.eq_equiv.
  Hint Extern 20 => solve [order].

  Definition IsOk s := Sort s.

  Class Ok (s:t A) : Prop := ok : Sort s.

  Hint Resolve ok.
  Hint Unfold Ok.

  Instance Sort_Ok s `(Hs : Sort s) : Ok s := { ok := Hs }.

  Lemma inf_iff : forall k (l : t A), Inf k l <-> inf k l = true.
  Proof.
    intros k l; split; intro H.
    (* -> *)
    induction l as [|(k',v) ls].
    reflexivity.
    simpl in *.
    apply HdRel_inv in H.
    rewrite <- compare_lt_iff in H. rewrite H; reflexivity.
    (* <- *)
    destruct l as [|(k',v) ys]; simpl in *.
      constructor; fail.
    revert H; case_eq (X.compare k k'); try discriminate; [].
    intros Ha _.
    rewrite compare_lt_iff in Ha.
    constructor; assumption.
  Qed.

  Lemma isok_iff : forall l, sort X.lt l <-> Ok l.
  Proof.
    intro l; split; intro H.
    (* -> *)
    elim H.
      constructor; fail.
    intros y ys Ha Hb Hc.
    change (inf y ys && isok ys = true).
    rewrite inf_iff in Hc.
    rewrite andb_true_iff; tauto.
    (* <- *)
    induction l as [|x xs].
      constructor.
    change (inf x xs && isok xs = true) in H.
    rewrite andb_true_iff, <- inf_iff in H.
    destruct H; constructor; tauto.
  Qed.

  Hint Extern 1 (Ok _) => rewrite <- isok_iff.

  Ltac inv_ok := match goal with
   | H:sort X.lt (_ :: _) |- _ => inversion_clear H; inv_ok
   | H:sort X.lt nil |- _ => clear H; inv_ok
   | H:sort X.lt ?l |- _ => change (Ok l) in H; inv_ok
   | H:Ok _ |- _ => rewrite <- isok_iff in H; inv_ok
   | |- Ok _ => rewrite <- isok_iff
   | _ => idtac
  end.

  Ltac inv := invlist InA; inv_ok; invlist lelistA.
  Ltac constructors := repeat constructor.

  Ltac sort_inf_in := match goal with
   | H:Inf ?x ?l, H':In ?y ?l |- _ =>
     cut (X.lt x y); [ intro | apply Sort_Inf_In with l; auto]
   | _ => fail
  end.

  Global Instance isok_Ok s `(isok s = true) : Ok s | 10.
  Proof.
  intros. assumption.
  Qed.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) := exists x, In x s /\ P x.

  Lemma mem_spec :
   forall (s : t) (x : elt) (Hs : Ok s), mem x s = true <-> In x s.
  Proof.
  induction s; intros x Hs; inv; simpl.
  intuition. discriminate. inv.
  elim_compare x a; rewrite InA_cons; intuition; try order.
  discriminate.
  sort_inf_in. order.
  rewrite <- IHs; auto.
  rewrite IHs; auto.
  Qed.

  Lemma add_inf :
   forall (s : t) (x a : elt), Inf a s -> X.lt a x -> Inf a (add x s).
  Proof.
  simple induction s; simpl.
  intuition.
  intros; elim_compare x a; inv; intuition.
  Qed.
  Hint Resolve add_inf.

  Global Instance add_ok s x : forall `(Ok s), Ok (add x s).
  Proof.
  repeat rewrite <- isok_iff; revert s x.
  simple induction s; simpl.
  intuition.
  intros; elim_compare x a; inv; auto.
  Qed.

  Lemma add_spec :
   forall (s : t) (x y : elt) (Hs : Ok s),
    In y (add x s) <-> X.eq y x \/ In y s.
  Proof.
  induction s; simpl; intros.
  intuition. inv; auto.
  elim_compare x a; inv; rewrite !InA_cons, ?IHs; intuition.
  Qed.

  Lemma remove_inf :
   forall (s : t) (x a : elt) (Hs : Ok s), Inf a s -> Inf a (remove x s).
  Proof.
  induction s; simpl.
  intuition.
  intros; elim_compare x a; inv; auto.
  apply Inf_lt with a; auto.
  Qed.
  Hint Resolve remove_inf.

  Global Instance remove_ok s x : forall `(Ok s), Ok (remove x s).
  Proof.
  repeat rewrite <- isok_iff; revert s x.
  induction s; simpl.
  intuition.
  intros; elim_compare x a; inv; auto.
  Qed.

  Lemma remove_spec :
   forall (s : t) (x y : elt) (Hs : Ok s),
    In y (remove x s) <-> In y s /\ ~X.eq y x.
  Proof.
  induction s; simpl; intros.
  intuition; inv; auto.
  elim_compare x a; inv; rewrite !InA_cons, ?IHs; intuition;
   try sort_inf_in; try order.
  Qed.

  Global Instance singleton_ok x : Ok (singleton x).
  Proof.
  unfold singleton; simpl; auto.
  Qed.

  Lemma singleton_spec : forall x y : elt, In y (singleton x) <-> X.eq y x.
  Proof.
  unfold singleton; simpl; split; intros; inv; auto.
  Qed.

  Ltac induction2 :=
    simple induction s;
     [ simpl; auto; try solve [ intros; inv ]
     | intros x l Hrec; simple induction s';
        [ simpl; auto; try solve [ intros; inv ]
        | intros x' l' Hrec'; simpl; elim_compare x x'; intros; inv; auto ]].

  Lemma union_inf :
   forall (s s' : t) (a : elt) (Hs : Ok s) (Hs' : Ok s'),
   Inf a s -> Inf a s' -> Inf a (union s s').
  Proof.
  induction2.
  Qed.
  Hint Resolve union_inf.

  Global Instance union_ok s s' : forall `(Ok s, Ok s'), Ok (union s s').
  Proof.
  repeat rewrite <- isok_iff; revert s s'.
  induction2; constructors; try apply @ok; auto. 
  apply Inf_eq with x'; auto; apply union_inf; auto; apply Inf_eq with x; auto; order.
  change (Inf x' (union (x :: l) l')); auto.
  Qed.

  Lemma union_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (union s s') <-> In x s \/ In x s'.
  Proof.
  induction2; try rewrite ?InA_cons, ?Hrec, ?Hrec'; intuition; inv; auto.
  Qed.

  Lemma inter_inf :
   forall (s s' : t) (a : elt) (Hs : Ok s) (Hs' : Ok s'),
   Inf a s -> Inf a s' -> Inf a (inter s s').
  Proof.
  induction2.
  apply Inf_lt with x; auto.
  apply Hrec'; auto.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve inter_inf.

  Global Instance inter_ok s s' : forall `(Ok s, Ok s'), Ok (inter s s').
  Proof.
  repeat rewrite <- isok_iff; revert s s'.
  induction2.
  constructors; auto.
  apply Inf_eq with x'; auto; apply inter_inf; auto; apply Inf_eq with x; auto.
  Qed.

  Lemma inter_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (inter s s') <-> In x s /\ In x s'.
  Proof.
  induction2; try rewrite ?InA_cons, ?Hrec, ?Hrec'; intuition; inv; auto;
   try sort_inf_in; try order.
  Qed.

  Lemma diff_inf :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (diff s s').
  Proof.
  intros s s'; repeat rewrite <- isok_iff; revert s s'.
  induction2.
  apply Hrec; trivial.
  apply Inf_lt with x; auto.
  apply Inf_lt with x'; auto.
  apply Hrec'; auto.
  apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve diff_inf.

  Global Instance diff_ok s s' : forall `(Ok s, Ok s'), Ok (diff s s').
  Proof.
  repeat rewrite <- isok_iff; revert s s'.
  induction2.
  Qed.

  Lemma diff_spec :
   forall (s s' : t) (x : elt) (Hs : Ok s) (Hs' : Ok s'),
   In x (diff s s') <-> In x s /\ ~In x s'.
  Proof.
  induction2; try rewrite ?InA_cons, ?Hrec, ?Hrec'; intuition; inv; auto;
   try sort_inf_in; try order.
  right; intuition; inv; auto.
  Qed.

  Lemma equal_spec :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s'),
   equal s s' = true <-> Equal s s'.
  Proof.
  induction s as [ | x s IH]; intros [ | x' s'] Hs Hs'; simpl.
  intuition.
  split; intros H. discriminate. assert (In x' nil) by (rewrite H; auto). inv.
  split; intros H. discriminate. assert (In x nil) by (rewrite <-H; auto). inv.
  inv.
  elim_compare x x' as C; try discriminate.
  (* x=x' *)
  rewrite IH; auto.
  split; intros E y; specialize (E y).
  rewrite !InA_cons, E, C; intuition.
  rewrite !InA_cons, C in E. intuition; try sort_inf_in; order.
  (* x<x' *)
  split; intros E. discriminate.
  assert (In x (x'::s')) by (rewrite <- E; auto).
  inv; try sort_inf_in; order.
  (* x>x' *)
  split; intros E. discriminate.
  assert (In x' (x::s)) by (rewrite E; auto).
  inv; try sort_inf_in; order.
  Qed.

  Lemma subset_spec :
   forall (s s' : t) (Hs : Ok s) (Hs' : Ok s'),
   subset s s' = true <-> Subset s s'.
  Proof.
  intros s s'; revert s.
  induction s' as [ | x' s' IH]; intros [ | x s] Hs Hs'; simpl; auto.
  split; try red; intros; auto.
  split; intros H. discriminate. assert (In x nil) by (apply H; auto). inv.
  split; try red; intros; auto. inv.
  inv. elim_compare x x' as C.
  (* x=x' *)
  rewrite IH; auto.
  split; intros S y; specialize (S y).
  rewrite !InA_cons, C. intuition.
  rewrite !InA_cons, C in S. intuition; try sort_inf_in; order.
  (* x<x' *)
  split; intros S. discriminate.
  assert (In x (x'::s')) by (apply S; auto).
  inv; try sort_inf_in; order.
  (* x>x' *)
  rewrite IH; auto.
  split; intros S y; specialize (S y).
  rewrite !InA_cons. intuition.
  rewrite !InA_cons in S. rewrite !InA_cons. intuition; try sort_inf_in; order.
  Qed.

  Global Instance empty_ok : Ok empty.
  Proof.
  constructors.
  Qed.

  Lemma empty_spec : Empty empty.
  Proof.
  unfold Empty, empty; intuition; inv.
  Qed.

  Lemma is_empty_spec : forall s : t, is_empty s = true <-> Empty s.
  Proof.
  intros [ | x s]; simpl.
  split; auto. intros _ x H. inv.
  split. discriminate. intros H. elim (H x); auto.
  Qed.

  Lemma elements_spec1 : forall (s : t) (x : elt), In x (elements s) <-> In x s.
  Proof.
  intuition.
  Qed.

  Lemma elements_spec2 : forall (s : t) (Hs : Ok s), sort X.lt (elements s).
  Proof.
  intro s; repeat rewrite <- isok_iff; auto.
  Qed.

  Lemma elements_spec2w : forall (s : t) (Hs : Ok s), NoDupA X.eq (elements s).
  Proof.
  intro s; repeat rewrite <- isok_iff; auto.
  Qed.

  Lemma min_elt_spec1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s.
  Proof.
  destruct s; simpl; inversion 1; auto.
  Qed.

  Lemma min_elt_spec2 :
   forall (s : t) (x y : elt) (Hs : Ok s),
   min_elt s = Some x -> In y s -> ~ X.lt y x.
  Proof.
  induction s as [ | x s IH]; simpl; inversion 2; subst.
  intros; inv; try sort_inf_in; order.
  Qed.

  Lemma min_elt_spec3 : forall s : t, min_elt s = None -> Empty s.
  Proof.
  destruct s; simpl; red; intuition. inv. discriminate.
  Qed.

  Lemma max_elt_spec1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s.
  Proof.
  induction s as [ | x s IH]. inversion 1.
  destruct s as [ | y s]. simpl. inversion 1; subst; auto.
  right; apply IH; auto.
  Qed.

  Lemma max_elt_spec2 :
   forall (s : t) (x y : elt) (Hs : Ok s),
   max_elt s = Some x -> In y s -> ~ X.lt x y.
  Proof.
  induction s as [ | a s IH]. inversion 2.
  destruct s as [ | b s]. inversion 2; subst. intros; inv; order.
  intros. inv; auto.
  assert (~X.lt x b) by (apply IH; auto).
  assert (X.lt a b) by auto.
  order.
  Qed.

  Lemma max_elt_spec3 : forall s : t, max_elt s = None -> Empty s.
  Proof.
  induction s as [ | a s IH]. red; intuition; inv.
  destruct s as [ | b s]. inversion 1.
  intros; elim IH with b; auto.
  Qed.

  Definition choose_spec1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s := min_elt_spec1.

  Definition choose_spec2 :
    forall s : t, choose s = None -> Empty s := min_elt_spec3.

  Lemma choose_spec3: forall s s' x x', Ok s -> Ok s' ->
   choose s = Some x -> choose s' = Some x' -> Equal s s' -> X.eq x x'.
  Proof.
   unfold choose; intros s s' x x' Hs Hs' Hx Hx' H.
   assert (~X.lt x x').
    apply min_elt_spec2 with s'; auto.
    rewrite <-H; auto using min_elt_spec1.
   assert (~X.lt x' x).
    apply min_elt_spec2 with s; auto.
    rewrite H; auto using min_elt_spec1.
   order.
  Qed.

  Lemma fold_spec :
   forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
   fold f s i = fold_left (flip f) (elements s) i.
  Proof.
  reflexivity.
  Qed.

  Lemma cardinal_spec :
   forall (s : t) (Hs : Ok s),
   cardinal s = length (elements s).
  Proof.
  auto.
  Qed.

  Lemma filter_inf :
   forall (s : t) (x : elt) (f : elt -> bool) (Hs : Ok s),
   Inf x s -> Inf x (filter f s).
  Proof.
  simple induction s; simpl.
  intuition.
  intros x l Hrec a f Hs Ha; inv.
  case (f x); auto.
  apply Hrec; auto.
  apply Inf_lt with x; auto.
  Qed.

  Global Instance filter_ok s f : forall `(Ok s), Ok (filter f s).
  Proof.
  repeat rewrite <- isok_iff; revert s f.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  case (f x); auto.
  constructors; auto.
  apply filter_inf; auto.
  Qed.

  Lemma filter_spec :
   forall (s : t) (x : elt) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (In x (filter f s) <-> In x s /\ f x = true).
  Proof.
  induction s; simpl; intros.
  split; intuition; inv.
  destruct (f a) eqn:F; rewrite !InA_cons, ?IHs; intuition.
  setoid_replace x with a; auto.
  setoid_replace a with x in F; auto; congruence.
  Qed.

  Lemma for_all_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof.
  unfold For_all; induction s; simpl; intros.
  split; intros; auto. inv.
  destruct (f a) eqn:F.
  rewrite IHs; auto. firstorder. inv; auto.
  setoid_replace x with a; auto.
  split; intros H'. discriminate.
  rewrite H' in F; auto.
  Qed.

  Lemma exists_spec :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof.
  unfold Exists; induction s; simpl; intros.
  firstorder. discriminate. inv.
  destruct (f a) eqn:F.
  firstorder.
  rewrite IHs; auto.
  firstorder.
  inv.
  setoid_replace a with x in F; auto; congruence.
  exists x; auto.
  Qed.

  Lemma partition_inf1 :
   forall (s : t) (f : elt -> bool) (x : elt) (Hs : Ok s),
   Inf x s -> Inf x (fst (partition f s)).
  Proof.
  intros s f x; repeat rewrite <- isok_iff; revert s f x.
  simple induction s; simpl.
  intuition.
  intros x l Hrec f a Hs Ha; inv.
  generalize (Hrec f a H).
  case (f x); case (partition f l); simpl.
  auto.
  intros; apply H2; apply Inf_lt with x; auto.
  Qed.

  Lemma partition_inf2 :
   forall (s : t) (f : elt -> bool) (x : elt) (Hs : Ok s),
   Inf x s -> Inf x (snd (partition f s)).
  Proof.
  intros s f x; repeat rewrite <- isok_iff; revert s f x.
  simple induction s; simpl.
  intuition.
  intros x l Hrec f a Hs Ha; inv.
  generalize (Hrec f a H).
  case (f x); case (partition f l); simpl.
  intros; apply H2; apply Inf_lt with x; auto.
  auto.
  Qed.

  Global Instance partition_ok1 s f : forall `(Ok s), Ok (fst (partition f s)).
  Proof.
  repeat rewrite <- isok_iff; revert s f.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (Hrec f H); generalize (@partition_inf1 l f x).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Global Instance partition_ok2 s f : forall `(Ok s), Ok (snd (partition f s)).
  Proof.
  repeat rewrite <- isok_iff; revert s f.
  simple induction s; simpl.
  auto.
  intros x l Hrec f Hs; inv.
  generalize (Hrec f H); generalize (@partition_inf2 l f x).
  case (f x); case (partition f l); simpl; auto.
  Qed.

  Lemma partition_spec1 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f -> Equal (fst (partition f s)) (filter f s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  split; auto.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  destruct (partition f l) as [s1 s2]; simpl; intros.
  case (f x); simpl; auto.
  split; inversion_clear 1; auto.
  constructor 2; rewrite <- H; auto.
  constructor 2; rewrite H; auto.
  Qed.

  Lemma partition_spec2 :
   forall (s : t) (f : elt -> bool),
   Proper (X.eq==>eq) f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
  simple induction s; simpl; auto; unfold Equal.
  split; auto.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  destruct (partition f l) as [s1 s2]; simpl; intros.
  case (f x); simpl; auto.
  split; inversion_clear 1; auto.
  constructor 2; rewrite <- H; auto.
  constructor 2; rewrite H; auto.
  Qed.

  End ForNotations.

  Definition In := InA X.eq.
  Instance In_compat : Proper (X.eq==>eq==> iff) In.
  Proof. repeat red; intros; rewrite H, H0; auto. Qed.

  Module L := MakeListOrdering X.
  Definition eq := L.eq.
  Definition eq_equiv := L.eq_equiv.
  Definition lt l1 l2 :=
    exists l1' l2', Ok l1' /\ Ok l2' /\ eq l1 l1' /\ eq l2 l2' /\ L.lt l1' l2'.

  Instance lt_strorder : StrictOrder lt.
  Proof.
  split.
  intros s (s1 & s2 & B1 & B2 & E1 & E2 & L).
  repeat rewrite <- isok_iff in *.
  assert (eqlistA X.eq s1 s2).
   apply SortA_equivlistA_eqlistA with (ltA:=X.lt); auto using @ok with *.
   transitivity s; auto. symmetry; auto.
  rewrite H in L.
  apply (StrictOrder_Irreflexive s2); auto.
  intros s1 s2 s3 (s1' & s2' & B1 & B2 & E1 & E2 & L12)
                  (s2'' & s3' & B2' & B3 & E2' & E3 & L23).
  exists s1', s3'.
  repeat rewrite <- isok_iff in *.
  do 4 (split; trivial).
  assert (eqlistA X.eq s2' s2'').
   apply SortA_equivlistA_eqlistA with (ltA:=X.lt); auto using @ok with *.
   transitivity s2; auto. symmetry; auto.
  transitivity s2'; auto.
  rewrite H; auto.
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  intros s1 s2 E12 s3 s4 E34. split.
  intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
  exists s1', s3'; do 2 (split; trivial).
   split. transitivity s1; auto. symmetry; auto.
   split; auto. transitivity s3; auto. symmetry; auto.
  intros (s1' & s3' & B1 & B3 & E1 & E3 & LT).
  exists s1', s3'; do 2 (split; trivial).
   split. transitivity s2; auto.
   split; auto. transitivity s4; auto.
  Qed.

  Lemma compare_spec_aux : forall s s', CompSpec eq L.lt s s' (compare s s').
  Proof.
  induction s as [|x s IH]; intros [|x' s']; simpl; intuition.
  elim_compare x x'; auto.
  Qed.

  Lemma compare_spec : forall s s', Ok s -> Ok s' ->
   CompSpec eq lt s s' (compare s s').
  Proof.
  intros s s' Hs Hs'.
  destruct (compare_spec_aux s s'); constructor; auto.
  exists s, s'; repeat split; auto using @ok.
  exists s', s; repeat split; auto using @ok.
  Qed.

End MakeRaw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we
   need to encapsulate everything into a type of strictly ordered lists. *)

Module Make (X: OrderedType) <: M with Module E := X.
 Module Raw := MakeRaw X.
 Include Raw2Sets X Raw.
End Make.


(** For this specific implementation, eq coincides with Leibniz equality *)

Require Eqdep_dec.

Module Type OrderedTypeWithLeibniz.
  Include OrderedType.
  Parameter eq_leibniz : forall x y, eq x y -> x = y.
End OrderedTypeWithLeibniz.

(*
TODO: eq?
Module Type SWithLeibniz.
  Declare Module E : OrderedTypeWithLeibniz.
  Include MapsOn E.
  Parameter eq_leibniz : forall x y, eq x y -> x = y.
End SWithLeibniz.

Module MakeWithLeibniz (X: OrderedTypeWithLeibniz) <: SWithLeibniz with Module E := X.
  Module E := X.
  Module Raw := MakeRaw X.
  Include Raw2SetsOn X Raw.

  Lemma eq_leibniz_list : forall xs ys, eqlistA X.eq xs ys -> xs = ys.
  Proof.
    induction xs as [|x xs]; intros [|y ys] H; inversion H; [ | ].
    reflexivity.
    f_equal.
    apply X.eq_leibniz; congruence.
    apply IHxs; subst; assumption.
  Qed.

  Lemma eq_leibniz : forall s s', eq s s' -> s = s'.
  Proof.
    intros [xs Hxs] [ys Hys] Heq.
    change (equivlistA X.eq xs ys) in Heq.
    assert (H : eqlistA X.eq xs ys).
      rewrite <- Raw.isok_iff in Hxs, Hys.
      apply SortA_equivlistA_eqlistA with X.lt; auto with *.
    apply eq_leibniz_list in H.
    subst ys.
    f_equal.
    apply Eqdep_dec.eq_proofs_unicity.
    intros x y; destruct (bool_dec x y); tauto.
  Qed.

End MakeWithLeibniz.
*)