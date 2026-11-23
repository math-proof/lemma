module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.EllipticCurves.code.LocalRingAtPoint

public section

open LocalRingAtPoint


/--
[isRegularAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/LocalRingAtPoint.lean)
-/
public theorem isRegularAt_iff
  [Field k]
  [Field K]
  [Algebra k K]
  {P : LocalRingAtPoint k K}
  {g : K} :
-- imply
  P.IsRegularAt g ↔ g ∈ P.toValuationSubring :=
-- proof
  Iff.rfl


/--
[algebraMap_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/LocalRingAtPoint.lean)
-/
public theorem algebraMap_mem_toValuationSubring
  [Field k]
  [Field K]
  [Algebra k K]
  {P : LocalRingAtPoint k K}
  {a : k} :
-- imply
  algebraMap k K a ∈ P.toValuationSubring := by
-- proof
  by_cases ha : a = 0
  · subst ha; simp [map_zero, P.toValuationSubring.zero_mem]
  · rw [← P.toValuationSubring.valuation_le_one_iff]
    rw [P.valuation_trivial_on_k a ha]


-- created on 2026-10-23
-- updated on 2026-11-23
