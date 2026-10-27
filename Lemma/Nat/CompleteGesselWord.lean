import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.CompleteGesselWord
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isCompleteGesselWord_iff_balance_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CompleteGesselWord.lean)
-/
@[path]
lemma isCompleteGesselWord_iff_balance_eq_zero
  {n : ℕ}
  {w : List (GesselAlphabet n)} :
-- imply
  IsCompleteGesselWord n w ↔
    IsGesselWord n w ∧ ∀ i : Fin n, gesselBalance n w (i.val + 1) = 0 := by
-- proof
  constructor
  · rintro ⟨hg, hcount⟩
    refine ⟨hg, fun i => ?_⟩
    have hi := hcount i
    unfold gesselBalance
    omega
  · rintro ⟨hg, hbalance⟩
    refine ⟨hg, fun i => ?_⟩
    have hi := hbalance i
    unfold gesselBalance at hi
    omega

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
