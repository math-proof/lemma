import Mathlib
import Lemma.ModularCurve.QAdicPlaceMod
import Lemma.ModularCurve.CharLFrobeniusGeomLevel
import Lemma.ModularCurve.SpecializeModuli
import Def.AlgebraicCurve_PlaceEvaluation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000


noncomputable section

open AlgebraicCurve Polynomial

namespace ModularCurve

variable (K : Type*) [Field K] in

def evalAtJGeom : Polynomial ℤ →+* LaurentSeries K :=
  Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K)


section Generators

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def jGeomGen : modularFunctionFieldC K N := ⟨jqModC K, jqModC_mem K N⟩

def jNGeomGen : modularFunctionFieldC K N := ⟨jqNModC K N, jqNModC_mem K N⟩

end Generators

section Evaluation

variable {R S : Type*} [CommRing R] [CommRing S]

def evalModularPair (x y : R) (Φ : Polynomial (Polynomial ℤ)) : R :=
  Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y

end Evaluation

section Centre

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def IsCentreOf (c : K × K) (w : Place K (modularFunctionFieldC K N)) : Prop :=
  0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) c.1) ∧
  0 < w.ord (jNGeomGen K N - algebraMap K (modularFunctionFieldC K N) c.2)

end Centre


section Existence

variable {K : Type*} [Field K] {N : ℕ} [NeZero N]

def IsAffineGeomPlace (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) : Prop :=
  jGeomGen K N ∈ w.toValuationSubring ∧ jNGeomGen K N ∈ w.toValuationSubring

end Existence

end ModularCurve

end
