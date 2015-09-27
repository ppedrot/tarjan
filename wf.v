Require Wellfounded SetoidList.
Require Import Morphisms Setoid List.

Section Wf.

Variable A : Type.
Variable eq : relation A.
Variable f : A -> list A.
Context {Heq : Equivalence eq} {HR : Proper (eq ==> Forall2 eq) f}.

Let R : relation A := fun x y => SetoidList.InA eq x (f x).

Variable set : list A.
Variable set_complete : forall x y, R x y -> SetoidList.InA eq x set.

Variable wf_R : well_founded R.

Lemma cycle : {x | Relation_Operators.clos_trans _ R x x}.
Proof.
Admitted.

End Wf.
