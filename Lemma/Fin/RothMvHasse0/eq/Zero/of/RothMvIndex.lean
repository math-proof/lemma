import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
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


-- updated on 2026-11-13
-- created on 2026-10-21
