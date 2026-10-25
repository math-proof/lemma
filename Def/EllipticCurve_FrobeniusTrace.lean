import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Valuation.RamificationGroup
import Instance.FLTPrelim_GaloisRep
import Def.FLTPrelim_Ramification
import Instance.EllipticCurve_FrobeniusTrace

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

variable (S) in

def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →* Module.End (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleEnd (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)


variable (S) in

def galoisTrace (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) : ZMod n :=
  LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) (galoisRepModuleEnd S W' n σ)

end WeierstrassCurve.Affine.Point

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup K) • x = x ^ q

end ValuationSubring

end
