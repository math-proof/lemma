import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CompleteGesselWord
open MetaMathlibExt


/--
[isCompleteGesselWord_iff_balance_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CompleteGesselWord.lean)
-/
@[path]
private lemma isCompleteGesselWord_iff_balance_eq_zero_eq
  {n : ℕ}
  {w : List (GesselAlphabet n)} :
-- imply
  IsCompleteGesselWord n w ↔
    IsGesselWord n w ∧ ∀ i : Fin n, gesselBalance n w (i.val + 1) = 0 := by
-- proof
  apply MetaMathlibExt.isCompleteGesselWord_iff_balance_eq_zero n w


-- created on 2026-10-20
