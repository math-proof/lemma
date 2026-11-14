import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothLastIndex_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (i : RothMvIndex n)
  (a : ℕ) :
-- imply
  rothLastIndex i a (Fin.last n) = a := by
-- proof
  have heq :
    (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simp [rothLastIndex]
    ext b
    simp [Finsupp.equivMapDomain_apply]
  have := congrArg (fun d : Finsupp (Option (Fin n)) ℕ ↦ d none) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this


-- updated on 2026-11-13
-- created on 2026-10-21
