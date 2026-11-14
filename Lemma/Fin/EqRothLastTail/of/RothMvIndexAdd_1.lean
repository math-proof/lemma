import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothLastTail_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (d : RothMvIndex (n + 1))
  (h : Fin n) :
-- imply
  rothLastTail d h = d h.castSucc := by
-- proof
  simp [rothLastTail, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]


-- updated on 2026-11-13
-- created on 2026-10-21
