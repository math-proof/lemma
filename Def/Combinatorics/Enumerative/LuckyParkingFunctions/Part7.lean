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
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part7


section

namespace MetaMathlibExt

def markedFun (n : ℕ) (a : Fin n → Fin n) (i0 : Fin n) :
    Fin (n + 1) → Fin (n + 1) :=
  fun k =>
    if h0 : k.val = 0 then ⟨0, by omega⟩
    else if h1 : k.val - 1 < i0.val then
      ⟨(a ⟨k.val - 1, by omega⟩).val, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩
    else
      ⟨(a ⟨k.val - 1, by omega⟩).val + 1, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩

end MetaMathlibExt
end
