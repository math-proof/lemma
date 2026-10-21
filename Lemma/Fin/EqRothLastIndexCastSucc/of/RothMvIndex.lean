import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothLastIndex_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (i : RothMvIndex n)
  (a : ℕ)
  (h : Fin n) :
-- imply
  rothLastIndex i a h.castSucc = i h := by
-- proof
  have heq :
    (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simp [rothLastIndex]
    ext b
    simp [Finsupp.equivMapDomain_apply]
  have := congrArg (fun d : Finsupp (Option (Fin n)) ℕ ↦ d (some h)) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this


-- created on 2026-10-21
