import Lemma.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Lemma.Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Lemma.Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open ModularCurve

variable {E V : Type} [Fintype E] [DecidableEq V]

namespace PeriodDatum

variable {D : DegeneracyData E V} {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}

def coeffMap (P : PeriodDatum D K L ord) (s : L →+* L) : P.TorusPoints →ₗ[ℤ] P.TorusPoints :=
  LinearMap.llcomp ℤ ↥(ribbonKernel D) (Additive Lˣ) (Additive Lˣ)
    (MonoidHom.toAdditive (Units.map (s : L →* L))).toIntLinearMap

@[simp] theorem coeffMap_apply (P : PeriodDatum D K L ord) (s : L →+* L) (u : P.TorusPoints)
    (z : ↥(ribbonKernel D)) :
    P.coeffMap s u z = Additive.ofMul (Units.map (s : L →* L) (Additive.toMul (u z))) := rfl

def precomp (P : PeriodDatum D K L ord) (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) :
    P.TorusPoints →ₗ[ℤ] P.TorusPoints :=
  LinearMap.lcomp ℤ (Additive Lˣ) f

@[simp] theorem precomp_apply (P : PeriodDatum D K L ord) (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D))
    (u : P.TorusPoints) (z : ↥(ribbonKernel D)) : P.precomp f u z = u (f z) := rfl

end PeriodDatum

structure PeriodUniformization [Fintype V] (r : ℕ) [Fact r.Prime] (D : DegeneracyData E V) (H : HeckeData D)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (T : Type) [AddCommGroup T] (hecke : HeckeAlg →+* Module.End ℤ T)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T) : Type 1 where

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

  heckeAdj : P.HeckeAdjointable H

  decomp_Q : ∀ (σ : ↥(A.decompositionSubgroup ℚ)) (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion),
    (∀ c, s c = σ • c) → ∀ x y : ↥(ribbonKernel D),
      s (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) =
        (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion)

  e : ↥P.U →+ T

  e_surj_torsion : ∀ t : T, IsOfFinAddOrder t → t ∈ e.range

  e_torsion : ∀ u : ↥P.U, IsOfFinAddOrder (e u)

  e_ker : ∀ u : ↥P.U, e u = 0 ↔ (u : P.TorusPoints) ∈ P.periodLattice

  e_hecke : ∀ (ℓ : Nat.Primes) (u : ↥P.U) (hu : P.precomp (heckeKernelMap H ℓ) (u : P.TorusPoints) ∈ P.U),
    e ⟨P.precomp (heckeKernelMap H ℓ) (u : P.TorusPoints), hu⟩ = hecke (heckeGen ℓ) (e u)

  e_inertia : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ (u : ↥P.U) (hu : P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints) ∈ P.U),
        e ⟨P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints), hu⟩ =
          gal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (e u)

  e_frob : ∀ φ : ↥(A.decompositionSubgroup ℚ),
    A.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) r →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = φ • c) →
      ∀ (u : ↥P.U) (hu : P.precomp (heckeKernelMap H ⟨r, Fact.out⟩)
          (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints)) ∈ P.U),
        e ⟨P.precomp (heckeKernelMap H ⟨r, Fact.out⟩)
            (P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : P.TorusPoints)), hu⟩ =
          gal (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (e u)

end Mumford
end CerednikDrinfeld

end
