import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFlip_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
-- given
  (r : Fin m → ℕ)
  (h : Fin m)
  (j : RothBox r) :
-- imply
  ((rothFlip r h j) h : ℕ) = r h - j h := by
-- proof
  simp [rothFlip]


-- created on 2026-10-21
