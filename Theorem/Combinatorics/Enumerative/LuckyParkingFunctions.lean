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
import Instance.Combinatorics.Enumerative.LuckyParkingFunctions.Part2


section

namespace MetaMathlibExt

lemma park_zero_val (m : ℕ) (a : Park m) (hm : 0 < m) :
    (a.1 ⟨0, hm⟩).val = 0 := by
  have h := a.2.2 ⟨0, hm⟩
  simp only at h
  omega

end MetaMathlibExt
end
