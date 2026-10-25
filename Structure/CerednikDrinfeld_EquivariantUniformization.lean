import Structure.CerednikDrinfeld_MumfordUniformization
import Instance.Compat_Mathlib430

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open ModularCurve

variable {E V : Type} [Fintype E] [DecidableEq V]

structure EquivariantUniformization (r : ℕ) [Fact r.Prime] (D : DegeneracyData E V)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (T : Type) [AddCommGroup T]
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))) (gal : S →* AddAut T) : Type 1 where

  K : IntermediateField ℚ A.valuation.Completion

  ord : Additive (↥K)ˣ →+ ℤ

  ord_spec : ∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
    Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k))

  inertia_K : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion)

  hensel_K : ∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k

  P : PeriodDatum D (↥K) A.valuation.Completion ord

  eFull : P.TorusPoints →+ T

  eFull_surjective : Function.Surjective eFull

  eFull_ker : ∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice

  Q_equiv : ∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q (actZ σ x) (actZ σ y)) : (↥K)ˣ) : ↥K) : A.valuation.Completion)

  eFull_equiv : ∀ (σ : S) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = (scalar σ) • c) → ∀ u : P.TorusPoints,
      eFull (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion)
        (P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) :
          ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u)) = gal σ (eFull u)

end Mumford
end CerednikDrinfeld

end
