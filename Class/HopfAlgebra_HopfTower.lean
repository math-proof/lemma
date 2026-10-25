import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open Coalgebra

universe u v w

namespace HopfAlgebra

class IsHopfTower (k : Type u) (A : Type v) (C : Type w) [CommRing k] [CommRing A] [CommRing C]
    [HopfAlgebra k A] [HopfAlgebra k C] [Algebra A C] [IsScalarTower k A C] : Prop where
  comul_algebraMap : ∀ a : A, comul (R := k) (algebraMap A C a) =
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A C) (IsScalarTower.toAlgHom k A C)
      (comul (R := k) a)
  counit_algebraMap : ∀ a : A, counit (R := k) (algebraMap A C a) = counit (R := k) a

end HopfAlgebra
