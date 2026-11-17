/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/CatalanTransformPair.lean -/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Rat.Star
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Catalan
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators


section

namespace MetaMathlibExt

noncomputable def CatQ : PowerSeries ℚ :=
  PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries

noncomputable def CatF : PowerSeries ℚ := PowerSeries.X * CatQ

noncomputable def CatG : PowerSeries ℚ := PowerSeries.X - PowerSeries.X ^ 2

end MetaMathlibExt
end
