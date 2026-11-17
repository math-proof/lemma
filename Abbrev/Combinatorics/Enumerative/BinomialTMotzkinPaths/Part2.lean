/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.BinomialTMotzkinPaths.Part2

@[expose] public section


section

open scoped BigOperators

namespace MetaMathlibExt

noncomputable abbrev binomialTMotzkinPS (t : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => ((((binomialTMotzkinCount t n 0 : ℕ))) : ℚ))

end MetaMathlibExt
end
