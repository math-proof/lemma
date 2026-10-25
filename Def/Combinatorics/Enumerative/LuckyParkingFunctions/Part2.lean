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
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part2


section

namespace MetaMathlibExt

def splitUpper (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) (hi : a i0 = i0) : Fin (n - i0.val) → Fin (n - i0.val) :=
  fun k => ⟨(a ⟨i0.val + k.val, by omega⟩).val - i0.val, by
    have hmon : i0 ≤ a ⟨i0.val + k.val, by omega⟩ := by
      calc i0 = a i0 := hi.symm
        _ ≤ a ⟨i0.val + k.val, by omega⟩ := ha.1 (by rw [Fin.le_def]; simp only; omega)
    have hle : i0.val ≤ (a ⟨i0.val + k.val, by omega⟩).val := Fin.le_def.mp hmon
    have hlt : (a ⟨i0.val + k.val, by omega⟩).val < n := (a _).isLt
    omega⟩

end MetaMathlibExt
end
