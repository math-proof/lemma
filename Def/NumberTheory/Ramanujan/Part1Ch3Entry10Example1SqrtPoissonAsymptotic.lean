/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SqrtPoissonAsymptotic.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Finset.Range
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example1SqrtPoissonAsymptotic

namespace Aux

/-- Degree-5 Taylor polynomial of sqrt(1+u). -/
noncomputable def P5 (u : ℝ) : ℝ :=
  1 + u/2 - u^2/8 + u^3/16 - 5*u^4/128 + 7*u^5/256

/-- Poisson weights. -/
noncomputable def pw (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

-- Error terms E_n = P5(u_n) - s_n.
noncomputable def TErr (x : ℝ) (n : ℕ) : ℝ :=
  P5 (((n:ℝ)-x)/x) - Real.sqrt ((n:ℝ)/x)

end Aux
end Entry10Example1SqrtPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
