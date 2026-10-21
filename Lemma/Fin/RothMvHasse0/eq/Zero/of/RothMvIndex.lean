import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvHasse_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommSemiring R]
  (i : RothMvIndex m) :
-- imply
  rothMvHasse i (0 : MvPolynomial (Fin m) R) = 0 := by
-- proof
  simp [rothMvHasse]


-- created on 2026-10-21
