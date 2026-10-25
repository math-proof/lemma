import Abbrev.CerednikDrinfeld_HeckeTower
import Instance.CerednikDrinfeld_MumfordQuotient
import Instance.CerednikDrinfeld_DrinfeldHolomorphic
import Def.ValuationSubring_CompletionRatClosure
import Instance.ValuationSubring_CompletionDecompositionAction
import Instance.EllipticCurve_FrobeniusTrace

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.Mumford CerednikDrinfeld.Omega AlgebraicCurve

namespace CerednikDrinfeld

def DescentIntertwining

    {q q' : ℕ} (r : ℕ) (ir irbar : Fin 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [Fact (A.DecompositionIsometric ℚ)]
    [DecidableEq A.valuation.Completion]

    {a b : ℚ}
    (ρ : (ℍ[ℚ, a, b])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A)))
    (ϖ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A) A.valuation.Completion)
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    (Γ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a, b])ˣ)

    (w wbar : HeckeTower.Obj q q' → (ℍ[ℚ, a, b])ˣ)
    (s : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a, b])ˣ)

    (dIso : ↥(A.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A) A.valuation.Completion)

    (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀]
    (𝕋 : HeckeTower.TowerData q q' F₀)
    (gal₀ : ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) F₀)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) F₀)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    (χ : ↥(A.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ ρ)) : Prop :=

  (∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → χ τ = 1) ∧
  (∀ φ : ↥(A.decompositionSubgroup ℚ),
      A.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) r → χ φ ≠ 1) ∧
  (∀ τ : ↥(A.decompositionSubgroup ℚ), χ τ = 1 ↔
      ∀ x : IsLocalRing.ResidueField ↥A, x ^ (r ^ 2) = x → τ • x = x) ∧

  (∀ (j : HeckeTower.Obj q q') (z : AlgebraicClosure ℚ),
      ιM j (algebraMap (AlgebraicClosure ℚ) (𝕋.objField j) z)
        = algebraMap A.valuation.Completion (FractionRing (Omega.HolRingOf ϖ ρ))
            ((z : AlgebraicClosure ℚ) : A.valuation.Completion)) ∧
  (∀ j : HeckeTower.Obj q q',
      Subfield.closure (Set.range (algebraMap A.valuation.Completion (FractionRing (Omega.HolRingOf ϖ ρ))) ∪ Set.range (ιM j))
        = Mumford.invariantFieldOf A.valuation.Completion (ℍ[ℚ, a, b])ˣ (Omega.HolRingOf ϖ ρ) (Γ j)) ∧
  (∀ (j : HeckeTower.Obj q q') (t : Finset (𝕋.objField j)),
      LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : 𝕋.objField j)) →
      LinearIndependent A.valuation.Completion (fun x : t => ιM j (x : 𝕋.objField j))) ∧

  (∀ (τ : ↥(A.decompositionSubgroup ℚ)) (x : F₀),
      ιM none (gal₀ τ • x)
        = (if χ τ = 1 then (1 : (ℍ[ℚ, a, b])ˣ) else w none)
            • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ (dIso τ)) (ιM none x)) ∧
  (∀ (ℓ : HeckeTower.AwayPrime q q') (τ : ↥(A.decompositionSubgroup ℚ)) (x : 𝕋.F ℓ),
      ιM (some ℓ) (galT ℓ τ • x)
        = (if χ τ = 1 then (1 : (ℍ[ℚ, a, b])ˣ) else w (some ℓ))
            • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ (dIso τ)) (ιM (some ℓ) x)) ∧

  (∀ x : F₀, ιM none (W ir • x) = w none • ιM none x) ∧
  (∀ x : F₀, ιM none (W irbar • x) = wbar none • ιM none x) ∧
  (∀ (ℓ : HeckeTower.AwayPrime q q') (x : 𝕋.F ℓ), ιM (some ℓ) (WT ℓ ir • x) = w (some ℓ) • ιM (some ℓ) x) ∧
  (∀ (ℓ : HeckeTower.AwayPrime q q') (x : 𝕋.F ℓ), ιM (some ℓ) (WT ℓ irbar • x) = wbar (some ℓ) • ιM (some ℓ) x) ∧

  (∀ (ℓ : HeckeTower.AwayPrime q q') (x : F₀), ιM (some ℓ) (𝕋.φ (ℓ, 0) x) = ιM none x) ∧
  (∀ (ℓ : HeckeTower.AwayPrime q q') (x : F₀), ιM (some ℓ) (𝕋.φ (ℓ, 1) x) = (s ℓ) • ιM none x)

end CerednikDrinfeld

end
