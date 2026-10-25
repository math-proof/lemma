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
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part3


section

namespace MetaMathlibExt

def joinFun (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) : Fin n → Fin n :=
  fun j =>
    if h : j.val < i0.val then
      ⟨(l.1 ⟨j.val, h⟩).val, by
        have h1 := (l.1 ⟨j.val, h⟩).isLt
        have h2 := i0.isLt
        omega⟩
    else
      ⟨(u.1 ⟨j.val - i0.val, by
        have hj := j.isLt
        have hi := i0.isLt
        omega⟩).val + i0.val, by
        have h1 := (u.1 ⟨j.val - i0.val, by
          have hj := j.isLt
          have hi := i0.isLt
          omega⟩).isLt
        have hi := i0.isLt
        omega⟩

end MetaMathlibExt
end
