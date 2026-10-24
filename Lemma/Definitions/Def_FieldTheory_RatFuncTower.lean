import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Rat

set_option autoImplicit false

noncomputable section

namespace RatFuncTower

abbrev K0 : Type := FractionRing (Polynomial (AlgebraicClosure ℚ))

scoped instance algebraRatPoly : Algebra (Polynomial ℚ) K0 :=
  ((algebraMap (Polynomial (AlgebraicClosure ℚ)) K0).comp
    (Polynomial.mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).toAlgebra

theorem algebraMap_ratPoly_apply (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) K0 p =
      algebraMap (Polynomial (AlgebraicClosure ℚ)) K0
        (p.map (algebraMap ℚ (AlgebraicClosure ℚ))) := rfl

def galLift (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : K0 ≃ₐ[Polynomial ℚ] K0 :=
  AlgEquiv.ofRingEquiv
    (f := IsFractionRing.ringEquivOfRingEquiv
      (A := Polynomial (AlgebraicClosure ℚ)) (B := Polynomial (AlgebraicClosure ℚ))
      (K := K0) (L := K0) (Polynomial.mapAlgEquiv σ).toRingEquiv)
    (by
      intro p
      have hq : ∀ q : Polynomial (AlgebraicClosure ℚ),
          (Polynomial.mapAlgEquiv σ).toRingEquiv q =
            q.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) := fun q => rfl
      rw [algebraMap_ratPoly_apply, IsFractionRing.ringEquivOfRingEquiv_algebraMap, hq,
        Polynomial.map_map]
      congr 2
      ext x
      simp)

theorem galLift_algebraMap (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : Polynomial (AlgebraicClosure ℚ)) :
    galLift σ (algebraMap (Polynomial (AlgebraicClosure ℚ)) K0 p) =
      algebraMap (Polynomial (AlgebraicClosure ℚ)) K0
        (p.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by
  simp [galLift]

end RatFuncTower

end
