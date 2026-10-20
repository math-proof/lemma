import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.Lie.WittMultigradedDimension
open scoped BigOperators
open MetaMathlibExt


/--
[finrank_freeLieMultihomogeneousComponent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma finrank_freeLieMultihomogeneousComponent_eq
  [Field K]
  {r : ℕ}
  {degree : Fin r → ℕ}
-- given
  (hdegree : 0 < ∑ i, degree i) :
-- imply
  (Module.finrank K (freeLieMultihomogeneousComponent K degree) : ℚ) =
    wittMultigradedValue degree := by
-- proof
  apply MetaMathlibExt.finrank_freeLieMultihomogeneousComponent K degree hdegree

/--
[witt_multigraded_dimension_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean)
-/
@[path]
private lemma witt_multigraded_dimension_formula_eq
  [Field K]
  {r : ℕ}
  {degree : Fin r → ℕ}
-- given
  (hr : 0 < r)
  (hdegree : 0 < ∑ i, degree i) :
-- imply
  (Module.finrank K (freeLieMultihomogeneousComponent K degree) : ℚ) =
    wittMultigradedValue degree := by
-- proof
  apply MetaMathlibExt.witt_multigraded_dimension_formula K r hr degree hdegree


-- created on 2026-10-20
