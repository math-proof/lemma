/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15InverseSeries.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

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
