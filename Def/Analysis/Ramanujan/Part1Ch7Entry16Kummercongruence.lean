/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry16Kummercongruence.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch7Phi
public import Theorem.Analysis.Ramanujan.Part1Ch7DirichletBeta
public import Theorem.Complex.Part1Ch7DirichletBeta
public import Theorem.Nat.LSeries.AbelContinuation
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.NumberTheory.LSeries.AbelContinuation

@[expose] public section

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
