/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry16Kummercongruence.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Def.Analysis.Ramanujan.Part1Ch7Phi
import Theorem.Analysis.Ramanujan.Part1Ch7DirichletBeta
import Lemma.Complex.Part1Ch7DirichletBeta
import Lemma.Nat.LSeries.AbelContinuation
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.NumberTheory.LSeries.AbelContinuation
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry16Kummercongruence

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry16Left (r : ℂ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : ℂ :=
  (chapter7Phi r ⟨x - 1, by constructor <;> linarith⟩ +
      chapter7Phi r ⟨-x, by constructor <;> linarith⟩ - 2 * riemannZeta (-r)) /
    (4 * Complex.Gamma (r + 1))

def chapter7Entry16Term (r : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (Real.cos (2 * Real.pi * k * x) : ℂ) /
    Complex.cpow (((2 * Real.pi * k : ℝ) : ℂ)) (r + 1)

def chapter7Entry16PartialSum (r : ℂ) (x : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 N, chapter7Entry16Term r x k

/-- Cosine-series coefficients with vanishing zeroth term, for Abel summation. -/
noncomputable def entry16Coeff (x : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then 0 else ((Real.cos (2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ)

end
end Entry16Kummercongruence
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
