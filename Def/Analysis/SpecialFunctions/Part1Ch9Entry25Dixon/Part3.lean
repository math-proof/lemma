/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Data.Finset.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Basic
public import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry25Dixon.Part2

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry25Dixon

open scoped Topology

open Filter

noncomputable section

def dixonM (u : ℂ) : ℂ :=
  ∑' j : ℕ, u ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))

def dixonLi (u : ℂ) : ℂ :=
  ∑' j : ℕ, dixonL u j

end
end Entry25Dixon
end Ramanujan.Part1Ch9
end
