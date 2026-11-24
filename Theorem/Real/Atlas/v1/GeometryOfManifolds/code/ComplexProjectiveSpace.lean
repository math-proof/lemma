module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.v1.Atlas.GeometryOfManifolds.code.ComplexProjectiveSpace.Part2


public section

/--
[CPn_fubiniStudy_not_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ComplexProjectiveSpace.lean)
-/
@[path]
private theorem CPn_fubiniStudy_not_exact_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ¬ DifferentialFormSpace.IsExact' (CPn_VF n) (CPn_fubiniStudy n) := by
-- proof
  apply CPn_fubiniStudy_not_exact n hn

/--
[CPn_fubiniStudy_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ComplexProjectiveSpace.lean)
-/
@[path]
private theorem CPn_fubiniStudy_nonzero_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  CPn_fubiniStudy n ≠ 0 := by
-- proof
  apply CPn_fubiniStudy_nonzero n hn


-- created on 2026-10-23
