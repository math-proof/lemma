/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part10


section

namespace MetaMathlibExt

def unplainFun (n : ℕ) (b : Park (n + 1))
    (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) :
    Fin n → Fin n :=
  fun j =>
    ⟨(b.1 ⟨j.val + 1, by omega⟩).val, by
      have hpos :
          0 < (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
        simp only
        omega
      have hNe := hNo ⟨j.val + 1, by omega⟩ hpos
      have hb := b.2.2 ⟨j.val + 1, by omega⟩
      simp only at hb
      have hval_ne :
          (b.1 ⟨j.val + 1, by omega⟩).val ≠
            (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
        intro hEq
        exact hNe (Fin.ext hEq)
      simp only at hval_ne
      omega⟩

end MetaMathlibExt
end
