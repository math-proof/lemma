import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
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


-- updated on 2026-11-13
-- created on 2026-10-21
