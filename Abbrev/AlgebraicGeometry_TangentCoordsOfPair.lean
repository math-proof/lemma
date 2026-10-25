import Mathlib
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Instance.AlgebraicGeometry_SquareZeroDeformation
import Def.AlgebraicGeometry_SquareZeroRelTangent
import Abbrev.AlgebraicGeometry_SmallExtensionPairTangent

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace RelTangentPoints

variable {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))

abbrev base : Z ⟶ Spec (CommRingCat.of k) := q₂ ≫ SquareZero.toBase k V


end RelTangentPoints

namespace SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

abbrev reductionBase : Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) ⟶ Spec (CommRingCat.of (ResidueField T')) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C)))

variable (T') in

abbrev thickeningFst :
    Spec (CommRingCat.of (thickening T' V C)) ⟶ Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom))

variable (T') in

abbrev thickeningSnd : Spec (CommRingCat.of (thickening T' V C)) ⟶ SquareZero.spec (ResidueField T') V :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
      (B := TrivSqZeroExt (ResidueField T') V)).toRingHom)


end SmallExtension

end AlgebraicGeometry

end
