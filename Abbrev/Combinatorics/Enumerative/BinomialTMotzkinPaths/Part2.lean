/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.BinomialTMotzkinPaths.Part2


section

open scoped BigOperators

namespace MetaMathlibExt

noncomputable abbrev binomialTMotzkinPS (t : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ))

end MetaMathlibExt
end
