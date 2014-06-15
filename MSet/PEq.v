Require Import Coq.Classes.RelationClasses.

Module Type PTyp.
  Parameter Inline(10) t : Type -> Type.
End PTyp.

Module Type HasPEq (Import T:PTyp).
  Parameter A: Type.
  Parameter Inline(30) eq :t A -> t A -> Prop.
End HasPEq.

Module Type PEq := PTyp <+ HasPEq.

Module Type IsPEq (Import E:PEq).
  Declare Instance eq_equiv : Equivalence eq.
End IsPEq.

