import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open TensorProduct IsLocalRing CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

abbrev thickening : Type u := (ResidueField T' ⊗[T'] C) ⊗[ResidueField T'] TrivSqZeroExt (ResidueField T') V

end AlgebraicGeometry.SmallExtension

end
