/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/CatalanTransformPair.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

section
namespace MetaMathlibExt

private noncomputable def CatQ : PowerSeries ℚ :=
  PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries

private noncomputable def CatF : PowerSeries ℚ := PowerSeries.X * CatQ
private noncomputable def CatG : PowerSeries ℚ := PowerSeries.X - PowerSeries.X ^ 2
end MetaMathlibExt
end
