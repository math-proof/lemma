/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.BellPermutationsSecondKind.Part3


namespace MetaMathlibExt

/-- Restrict an RGF on `Fin (n+1)` to its first `n` coordinates. -/
def restr {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) : Fin n → Fin n :=
  fun i => ⟨(f i.castSucc).val, by
    have h := rgf_subdiag hf i.castSucc
    rw [Fin.val_castSucc] at h
    exact lt_of_le_of_lt h i.isLt⟩

end MetaMathlibExt
