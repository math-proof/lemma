import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Minpoly.IntegrallyClosed
open minpoly


/--
[isIntegral_iff_mem_lifts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Minpoly/IntegrallyClosed.lean)
-/
@[path]
private lemma isIntegral_iff_mem_lifts_eq
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  {x : L}
-- given
  (hx : IsAlgebraic K x) :
-- imply
  IsIntegral R x ↔ minpoly K x ∈ Polynomial.lifts (algebraMap R K) := by
-- proof
  apply minpoly.isIntegral_iff_mem_lifts hx

/--
[isIntegral_iff_coeff_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Minpoly/IntegrallyClosed.lean)
-/
@[path]
private lemma isIntegral_iff_coeff_mem_range_eq
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  {x : L}
-- given
  (hx : IsAlgebraic K x) :
-- imply
  IsIntegral R x ↔ ∀ n, (minpoly K x).coeff n ∈ Set.range (algebraMap R K) := by
-- proof
  apply minpoly.isIntegral_iff_coeff_mem_range hx


-- created on 2026-10-20
