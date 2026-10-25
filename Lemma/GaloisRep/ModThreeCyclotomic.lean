import Mathlib
import Lemma.FreyPackage.DetCyclotomic
import Def.GaloisRep_ModThreeCyclotomic

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine.Point


@[simp] lemma modThreeCyclotomicChar_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    modThreeCyclotomicChar σ = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :=
  rfl

end WeierstrassCurve
