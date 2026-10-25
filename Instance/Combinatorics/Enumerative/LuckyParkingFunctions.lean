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
import Abbrev.Combinatorics.Enumerative.LuckyParkingFunctions


section

namespace MetaMathlibExt

instance Park.decidablePred (n : ℕ) :
    DecidablePred (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val) :=
  fun _ => inferInstance

instance Park.fintype (n : ℕ) : Fintype (Park n) := Subtype.fintype _

end MetaMathlibExt
end
