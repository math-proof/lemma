/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry20Piseries1.lean -/

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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9CosineFourierThreeTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  Real.cos (2 * (k : ℝ) * x) / ((k : ℝ) ^ 3)

def chapter9Entry20LogTerm (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 / 2 * Real.log |2 * Real.sin x|

def chapter9Entry23FactorialTerm (u : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
    (((2 * k + 1).factorial : ℝ) * (((2 * k + 2 : ℕ) : ℝ) ^ 2))

def chapter9SineFourierTwoTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  Real.sin (2 * (k : ℝ) * x) / ((k : ℝ) ^ 2)

def chapter9ZetaThreeTerm (j : ℕ) : ℝ :=
  let k := j + 1
  1 / ((k : ℝ) ^ 3)

def chapter9ZetaThree : ℝ :=
  ∑' j : ℕ, chapter9ZetaThreeTerm j

private def auxA (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ))

private def auxP_term (s : ℝ) (k : ℕ) : ℝ := auxA k * s ^ (2 * k + 1)

private def auxP (s : ℝ) : ℝ := ∑' k : ℕ, auxP_term s k

private def auxPderiv_term (s : ℝ) (k : ℕ) : ℝ :=
  auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k)

private def auxK (x : ℝ) : ℝ := Real.cos x * auxP (Real.sin x)

private def auxH_term (x : ℝ) (k : ℕ) : ℝ :=
  auxA k * Real.sin x ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ))

private def auxH (x : ℝ) : ℝ := ∑' k : ℕ, auxH_term x k

private def auxF (x : ℝ) : ℝ := ∑' k : ℕ, chapter9Entry23FactorialTerm x k

private def auxAr_term (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (j + 1) * Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2)

private def auxAr (r x : ℝ) : ℝ := ∑' j : ℕ, auxAr_term r x j

private def auxAr_deriv_term (r x : ℝ) (j : ℕ) : ℝ :=
  2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))

private def auxZ (r x : ℝ) : ℂ := ⟨r * Real.cos (2 * x), r * Real.sin (2 * x)⟩

private def auxA_fourier (x : ℝ) : ℝ := ∑' j : ℕ, chapter9SineFourierTwoTerm x j

private def auxAr_deriv (r x : ℝ) : ℝ := ∑' j : ℕ, auxAr_deriv_term r x j

private def auxA_deriv_lim (x : ℝ) : ℝ := -Real.log (4 * Real.sin x ^ 2)

private def auxB_fourier (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter9CosineFourierThreeTerm x j

private def auxG (x : ℝ) : ℝ :=
  chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
    (1 / 4 : ℝ) * auxB_fourier x - chapter9ZetaThree / 4
end
end Entry20Piseries1
end MathlibExt.Analysis.Ramanujan.Part1Ch9
