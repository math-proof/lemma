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
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part8


section

namespace MetaMathlibExt

def embedMarked (n : ℕ) (m : Marked n) : Park (n + 1) :=
  ⟨markedFun n m.1.1 m.2.1, markedFun_mono n m.1.1 m.1.2 m.2.1,
    fun k => markedFun_bound n m.1.1 m.1.2 m.2.1 k⟩

end MetaMathlibExt
end
