/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example2LogPoissonAsymptotic.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example2LogPoissonAsymptotic

/-- Poisson weight: `w x M = e ^ (-x) * x ^ M / M !`. -/
private noncomputable def w (x : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-x) * x ^ M / (Nat.factorial M : ℝ)

/-- Fifth-order Taylor polynomial of `log (1 + u)` at `u = 0`. -/
private noncomputable def P (u : ℝ) : ℝ := u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5

/-- Taylor remainder `log y - P (y - 1)`. -/
private noncomputable def hlog (y : ℝ) : ℝ := Real.log y - P (y - 1)

/-- Upper barrier `hlog y + (y-1)^6/6` for `y ≥ 1`. -/
private noncomputable def g2 (y : ℝ) : ℝ := hlog y + (y - 1) ^ 6 / 6

/-- Lower barrier `hlog y + (1-y)^6/(6y)` for `0 < y ≤ 1`. -/
private noncomputable def Kf (y : ℝ) : ℝ := hlog y + (1 - y) ^ 6 / (6 * y)
end Entry10Example2LogPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
