import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFinsuppL1_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (a : α)
  (c : ℤ) :
-- imply
  rothFinsuppL1 (Finsupp.single a c) = c.natAbs := by
-- proof
  classical
  if hc : c = 0 then
    simp [hc, rothFinsuppL1]
  else
    simp [rothFinsuppL1, hc]


-- created on 2026-10-21
