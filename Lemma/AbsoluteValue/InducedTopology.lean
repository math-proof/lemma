import Mathlib
import sympy.Basic
import sympy.Analysis.AbsoluteValue.InducedTopology

open AbsoluteValue

/--
[inducedTopology_eq_iff_isEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/AbsoluteValue/InducedTopology.lean)
-/
@[path]
private lemma inducedTopology_eq_iff_isEquiv_eq
  [Field K]
-- given
  (v w : AbsoluteValue K ℝ) :
-- imply
  v.inducedTopology = w.inducedTopology ↔ v.IsEquiv w := by
-- proof
  apply AbsoluteValue.inducedTopology_eq_iff_isEquiv


-- created on 2026-10-09
