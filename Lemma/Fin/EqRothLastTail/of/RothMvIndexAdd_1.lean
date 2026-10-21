import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
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


-- created on 2026-10-21
