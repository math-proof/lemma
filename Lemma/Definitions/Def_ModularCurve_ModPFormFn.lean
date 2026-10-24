import Mathlib
import Lemma.Definitions.Def_ModularCurve_PlaceWidth
import Lemma.Definitions.Def_ModularCurve_QExpansionDiff
set_option autoImplicit false

noncomputable section
open AlgebraicCurve

namespace ModularCurve

def thetaJ (K : Type*) [Field K] : LaurentSeries K := thetaL K (jqModC K)

def qexpOfWeight (K : Type*) [Field K] (m : ℤ) (G : LaurentSeries K) : LaurentSeries K :=
  G * thetaJ K ^ m

def stackOrd {K : Type*} [Field K] [DecidableEq K] (N : ℕ) [NeZero N] (m : ℤ)
    (G : ↥(modularFunctionFieldC K N)) (x : Place K (modularFunctionFieldC K N)) : ℤ :=
  (placeWidth N x : ℤ) * x.ord G + m * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1)

def IsModPFormFn (K : Type*) [Field K] (m : ℕ) (G : LaurentSeries K) : Prop :=
  IsIntegral (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (G ^ 6 * jqModC K ^ (4 * m) * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (3 * m)) ∧
    IsIntegral (Algebra.adjoin K ({(jqModC K)⁻¹} : Set (LaurentSeries K)))
      (G ^ 2 * jqModC K ^ m * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ m)

def IsModPCuspFormFn (K : Type*) [Field K] (m : ℕ) (G : LaurentSeries K) : Prop :=
  IsIntegral (Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (G ^ 6 * jqModC K ^ (4 * m) * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (3 * m)) ∧
    ∃ M : ℕ, IsIntegral (Algebra.adjoin K ({(jqModC K)⁻¹} : Set (LaurentSeries K)))
      (G ^ (2 * M) * jqModC K ^ (m * M + 1) * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (m * M))

end ModularCurve

end
