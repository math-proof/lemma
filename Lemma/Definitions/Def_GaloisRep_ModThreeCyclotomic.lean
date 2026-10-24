import Mathlib
import Lemma.Definitions.Def_FreyPackage_DetCyclotomic

set_option autoImplicit false

namespace WeierstrassCurve

open WeierstrassCurve.Affine.Point

noncomputable def modThreeCyclotomicChar :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod 3)ˣ :=
  MonoidHom.mk'
    (fun σ => modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (fun a b => by rw [← map_mul]; congr 1)

@[simp] lemma modThreeCyclotomicChar_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    modThreeCyclotomicChar σ = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) :=
  rfl

end WeierstrassCurve
