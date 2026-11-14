import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvOrder_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (h : Fin m) (n : ℕ) :
-- imply
  rothMvOrder (Finsupp.single h n) = n := by
-- proof
  simp [rothMvOrder]


-- updated on 2026-11-13
-- created on 2026-10-21
