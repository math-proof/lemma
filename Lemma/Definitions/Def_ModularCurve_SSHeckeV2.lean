import Mathlib
import Lemma.Definitions.Def_ModularCurve_PlaceWidth
import Lemma.Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Lemma.Definitions.Def_ModularCurve_QExpansionDiff
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Lemma.Definitions.Def_ModularCurve_WeightDivisor
import Lemma.Definitions.Def_ModularCurve_SSCarrier

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section
open AlgebraicCurve ModularCurve

namespace ModularCurve
variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]

def heckeMultiplier (ℓ : ℕ) [NeZero ℓ] : ↥(charLDegeneracyRoof K N ℓ) :=
  Classical.epsilon (fun h : ↥(charLDegeneracyRoof K N ℓ) =>
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
    KaehlerDifferential.D K ↥(charLDegeneracyRoof K N ℓ) (heckeBetaC K N ℓ (jGeomGen K N))
      = h • KaehlerDifferential.map K K ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (KaehlerDifferential.D K ↥(modularFunctionFieldC K N) (jGeomGen K N)))

def liftFun (hp5 : 5 ≤ p) (k : ℤ) (v : SSCarrier p N K hp5 k) : ↥(modularFunctionFieldC K N) :=
  Classical.epsilon (fun g : ↥(modularFunctionFieldC K N) =>
    (∀ z : Place K (modularFunctionFieldC K N), z ∈ ssPlaces p N K →
        -((ModularCurve.weightDivisor K N (k / 2).toNat) z) ≤ z.ord g) ∧
    (∀ x : SSIndex p N K hp5 k, lead N K x.1 (poleOrder p N K hp5 k x) g = v x))

def ssHeckeFun (hp5 : 5 ≤ p) (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (v : SSCarrier p N K hp5 k) : SSCarrier p N K hp5 k :=
  fun x =>
    letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
    algebraMap K K ((ℓ : K) ^ (k / 2 - 1)) *
      lead N K x.1 (poleOrder p N K hp5 k x)
        (Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
          (heckeBetaC K N ℓ (liftFun p N K hp5 k v) * heckeMultiplier N K ℓ ^ (k / 2).toNat))

def resQFun (hp5 : 5 ≤ p) (k : ℤ) (φ : PowerSeries K) : SSCarrier p N K hp5 k :=
  fun x =>
    lead N K x.1 (poleOrder p N K hp5 k x)
      (Classical.epsilon (fun G : ↥(modularFunctionFieldC K N) =>
        (G : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K φ * thetaL K (jqModC K) ^ (-(k / 2))))

end ModularCurve
end
