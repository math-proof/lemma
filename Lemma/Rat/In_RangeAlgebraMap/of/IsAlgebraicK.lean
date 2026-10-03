import Mathlib
import sympy.Basic


/--
[AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic.lean)
-/
@[main]
private lemma main
  [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
  {x : L}
-- given
  (hx : IsAlgebraic K x) :
-- imply
  x ∈ (algebraMap K L).range :=
-- proof
  minpoly.degree_eq_one_iff.mp
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx.isIntegral))


-- created on 2026-10-03
