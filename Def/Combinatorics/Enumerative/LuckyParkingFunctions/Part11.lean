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
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part11


section

namespace MetaMathlibExt

def unmarkedFun (n : ℕ) (b : Park (n + 1)) (i0 : Fin n) :
    Fin n → Fin n :=
  fun j =>
    if h : j.val < i0.val then
      ⟨(b.1 ⟨j.val + 1, by omega⟩).val, by
        have hb := b.2.2 ⟨j.val + 1, by omega⟩
        simp only at hb
        have hi := i0.isLt
        omega⟩
    else
      ⟨(b.1 ⟨j.val + 1, by omega⟩).val - 1, by
        have hlt := (b.1 ⟨j.val + 1, by omega⟩).isLt
        omega⟩

end MetaMathlibExt
end
