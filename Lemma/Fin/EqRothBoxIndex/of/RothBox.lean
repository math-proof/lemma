import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothBoxIndex_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {r : Fin m → ℕ}
-- given
  (j : RothBox r)
  (h : Fin m) :
-- imply
  rothBoxIndex j h = j h := by
-- proof
  simp [rothBoxIndex]


-- created on 2026-10-21
