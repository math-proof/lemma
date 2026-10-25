/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15InverseSeries.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 15, inverse series

The branch `u < 1` of `u - log u = 1 + x ^ 2 / 2` as a convergent power series near `x = 0`, from
B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985).
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry15InverseSeries

open Filter Topology

noncomputable def hfun (t : ℝ) : ℝ := t - Real.log (1 + t)

end Entry15InverseSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
