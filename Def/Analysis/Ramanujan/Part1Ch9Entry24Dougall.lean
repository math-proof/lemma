/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry24Dougall.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9BoundaryLog (x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.log x

def chapter9DilogCosTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.cos ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

def chapter9DilogSinTerm (rho angle : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  rho ^ k * Real.sin ((k : ℝ) * angle) / ((k : ℝ) ^ 2)

def cLi2Term (z : ℂ) (j : ℕ) : ℂ :=
  z ^ (j + 1) / ((((j + 1 : ℕ)) : ℂ) ^ 2)

def cLi2 (z : ℂ) : ℂ :=
  ∑' j, cLi2Term z j

def cLi2DerivTerm (z : ℂ) (j : ℕ) : ℂ :=
  z ^ j / ((((j + 1 : ℕ)) : ℂ))

def cLi2Deriv (z : ℂ) : ℂ :=
  ∑' j, cLi2DerivTerm z j

def spenceFun (z : ℂ) : ℂ :=
  cLi2 z + cLi2 (1 - z) + Complex.log z * Complex.log (1 - z)

def openLens : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1

def seqT : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)

def seqU : ℕ → ℂ := fun n => ((seqT n : ℝ) : ℂ)

def closedLens : Set ℂ :=
  Metric.closedBall (0 : ℂ) 1 ∩ Metric.closedBall (1 : ℂ) 1

def blendSeq (z0 : ℂ) : ℕ → ℂ := fun n =>
  (((1 - seqT n : ℝ)) : ℂ) * z0 + ((((seqT n / 2 : ℝ))) : ℂ)

end
end Entry24Dougall
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
