/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example1SqrtPoissonAsymptotic.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Finset.Range
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example1SqrtPoissonAsymptotic

namespace Aux

/-- Degree-5 Taylor polynomial of sqrt(1+u). -/
private noncomputable def P5 (u : ℝ) : ℝ :=
  1 + u/2 - u^2/8 + u^3/16 - 5*u^4/128 + 7*u^5/256
/-- Poisson weights. -/
private noncomputable def pw (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

-- Error terms E_n = P5(u_n) - s_n.
private noncomputable def TErr (x : ℝ) (n : ℕ) : ℝ :=
  P5 (((n:ℝ)-x)/x) - Real.sqrt ((n:ℝ)/x)
end Aux
end Entry10Example1SqrtPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
