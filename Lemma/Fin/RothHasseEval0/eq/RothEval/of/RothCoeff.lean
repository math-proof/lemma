import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_hasseEval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  {r : Fin m → ℕ}
-- given
  (c : RothCoeff r)
  (x : Fin m → R) :
-- imply
  rothHasseEval c 0 x = rothEval c x := by
-- proof
  simp [rothHasseEval, rothEval]


-- updated on 2026-11-13
-- created on 2026-10-21
