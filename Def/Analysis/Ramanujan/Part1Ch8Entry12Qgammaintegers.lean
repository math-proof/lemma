/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry12Qgammaintegers.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry12Qgammaintegers

open scoped Interval

open MeasureTheory

noncomputable section

def chapter8UnitPow (x : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0 else Complex.exp (x * Real.log u)

def chapter8Entry12Kernel (x : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0
  else if u = 1 then 0
  else
    chapter8UnitPow (x - 2) u * ((1 - u : ℝ) : ℂ) ^ 2 /
      (1 - chapter8UnitPow x u)

def chapter8PhiTerm (x : ℂ) (j : ℕ) : ℂ :=
  let k := j + 1
  2 / ((((k : ℂ) * x) ^ 3) - (k : ℂ) * x)

def chapter8Phi (x : ℂ) : ℂ :=
  1 + ∑' j : ℕ, chapter8PhiTerm x j

/-- Summand as a function of u: cpow form, defined everywhere. -/
def chapter8Fterm (x : ℂ) (j : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ ((((j + 1 : ℕ)) : ℂ) * x - 2) * (((1 - u : ℝ)) : ℂ) ^ 2

/-- Real majorant for dominated convergence. -/
def chapter8Bound (x : ℂ) (j : ℕ) (u : ℝ) : ℝ :=
  u ^ (x.re - 2) * u ^ ((j : ℝ)) * (1 - u) ^ 2

end
end Entry12Qgammaintegers
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
