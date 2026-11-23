/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry9Zetaeven.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
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
public import Theorem.Real.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
public import Theorem.Real.Ramanujan.Part1Ch7Entry8Bernoullibound
public import Abbrev.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
public import Def.Analysis.Ramanujan.Part1Ch7Entry8Bernoullibound
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry9Zetaeven

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

open Entry10Zetaviabernoulli (chapter7Admissible chapter7PowerDifferenceTerm)

open Entry8Bernoullibound (chapter7BernoulliPolynomial chapter7IntegerPhi)

noncomputable section

def chap7W (x : ℂ) (j : ℕ) : ℂ := x / ((j : ℂ) + 1)

def chap7R (K : ℕ) (r w : ℂ) : ℂ :=
  (1 + w) ^ r - ∑ k ∈ Finset.range (K + 1), Ring.choose r k * w ^ k

def chap7g (K J : ℕ) (x : ℂ) (n : ℕ) (r : ℂ) : ℂ :=
  -((((n + J : ℕ) : ℂ) + 1) ^ r * chap7R K r (chap7W x (n + J)))

def chap7U (m : ℕ) : Set ℂ := {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ)}

def chap7S (m N : ℕ) : Set ℂ :=
  {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ) ∧ ‖r‖ < (N : ℝ)}

def chap7G (K J : ℕ) (x : ℂ) (r : ℂ) : ℂ :=
  ∑' n : ℕ, chap7g K J x n r

def chap7E : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

def chap7P (k : ℕ) (r : ℂ) : ℂ :=
  ∏ i ∈ Finset.range (k - 1), (r - (i : ℂ))

def chap7H (J : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range J, ((((j : ℕ) : ℂ) + 1) ^ (-s))

def chap7T (x : ℂ) (j : ℕ) (r : ℂ) : ℂ :=
  ((((j : ℕ) : ℂ) + 1) ^ r - ((((j : ℕ) : ℂ) + 1 + x) ^ r))

def chap7PhiCont (K J : ℕ) (x : ℂ) (r : ℂ) : ℂ :=
  (∑ j ∈ Finset.range J, chap7T x j r) +
    (∑' n : ℕ, chap7g K J x n r) +
    ∑ k ∈ Finset.Icc 1 K,
      x ^ k * (chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
        Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r))

end
end Entry9Zetaeven
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
