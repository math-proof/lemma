import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothRidoutBoxComplement_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
-- given
  (r : Fin m → ℕ)
  (j : RothBox r)
  (h : Fin m) :
-- imply
  ((rothRidoutBoxComplement r j) h : ℕ) = r h - j h := by
-- proof
  rfl


-- created on 2026-10-21
