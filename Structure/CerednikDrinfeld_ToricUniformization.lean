import Structure.CerednikDrinfeld_JPrimeTorsionDatum
import Instance.Compat_Mathlib430
import Def.CerednikDrinfeld_ToricUniformization

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]


omit [Fintype V] in

structure ToricUniformization (p r : ℕ) [Fact r.Prime] (D : DegeneracyData E V) (H : HeckeData D)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T) : Type 1 where

  U : Type
  [instAddCommGroupU : AddCommGroup U]

  heckeU : HeckeAlg →+* Module.End ℤ U

  divisible : ∀ u : U, ∀ n : ℕ, 0 < n → ∃ u' : U, n • u' = u

  π : U →+ T

  π_hecke : ∀ (x : HeckeAlg) (u : U), π (heckeU x u) = hecke x (π u)

  π_surj_torsion : ∀ t : T, p • t = 0 → ∃ u : U, π u = t

  periodEquiv : ↥(ribbonKernel D) ≃+ ↥π.ker

  period_adjoint : ∀ (ℓ : Nat.Primes) (x y y' : ↥(ribbonKernel D)),
    heckeU (heckeGen ℓ) (periodEquiv y : U) = (periodEquiv y' : U) →
      ribbonGram D (heckeKernelMap H ℓ x) y = ribbonGram D x y'

  torsionEquiv : ↥(Submodule.torsionBy ℤ U (p : ℤ)) ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p)

  torsion_hecke : ∀ (ℓ : Nat.Primes) (v : ↥(Submodule.torsionBy ℤ U (p : ℤ)))
    (hv : heckeU (heckeGen ℓ) (v : U) ∈ Submodule.torsionBy ℤ U (p : ℤ)),
    torsionEquiv ⟨heckeU (heckeGen ℓ) (v : U), hv⟩ = (torsionEquiv v) ∘ₗ heckeKernelMap H ℓ

  tame : ↥(A.inertiaSubgroupIn ℚ) →* Multiplicative (ZMod p)

  tame_surjective : Function.Surjective tame

  kummer : ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (u : U) (x : ↥(ribbonKernel D)),
    (p : ℤ) • u = (periodEquiv x : U) →
      ∃ (v : ↥(Submodule.torsionBy ℤ U (p : ℤ))),
        gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (π u) = π u + π (v : U) ∧
        torsionEquiv v = (Multiplicative.toAdd (tame σ)) • ribbonGramModP p D x

  frob_toric : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
    ∀ v : ↥(Submodule.torsionBy ℤ U (p : ℤ)), ∃ v' : ↥(Submodule.torsionBy ℤ U (p : ℤ)),
      gal φ (π (v : U)) = π (v' : U) ∧
        torsionEquiv v' = (r : ℤ) • ((torsionEquiv v) ∘ₗ heckeKernelMap H ⟨r, Fact.out⟩)

  frob_quot : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ r →
    ∀ (u : U) (x : ↥(ribbonKernel D)), (p : ℤ) • u = (periodEquiv x : U) →
      ∃ v : U, (p : ℤ) • v = 0 ∧ gal φ (π u) = π (heckeU (heckeGen ⟨r, Fact.out⟩) u) + π v

end CerednikDrinfeld

end
