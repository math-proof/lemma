module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothLastTail_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.EqRothLastTail.of.RothMvIndexAdd_1
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
