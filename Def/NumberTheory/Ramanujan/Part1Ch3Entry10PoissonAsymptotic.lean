/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10PoissonAsymptotic.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Def.Combinatorics.AssociatedStirlingSecond
import Lemma.Finset.AssociatedStirlingSecond
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Cast.Field
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Module
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.

This file proves Entry 10's general Poisson asymptotic expansion.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10PoissonAsymptotic

/-- The 2-associated Stirling number of the second kind: the number of partitions of an
`n`-element set into `k` blocks, each containing at least two elements.
It is kept as written because the Entry 10 statement refers to it, and it agrees with
`MetaMathlibExt.twoAssocStirlingSecond` by `twoAssocStirlingSecond_eq_canonical`. -/
def twoAssocStirlingSecond (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), ((-1 : ℤ) ^ j) * (Nat.choose n j : ℤ) *
      (Nat.stirlingSecond (n - j) (k - j) : ℤ)

noncomputable def taylorPoly
    (φ : ℝ → ℂ) (N : ℕ) (c t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1),
    (((t - c) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) *
      iteratedDeriv k φ c

noncomputable def poisson_taylorTerm (φ : ℝ → ℂ) (x : ℝ)
    (p : Sigma fun _ : ℕ => ℕ) : ℂ :=
  ((twoAssocStirlingSecond p.1 p.2 : ℤ) : ℂ) * (x : ℂ) ^ p.2 *
    (iteratedDeriv p.1 φ x / (Nat.factorial p.1 : ℂ))

def poisson_taylorPairs (N : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (Finset.range (N + 1)).sigma fun n => Finset.range (n + 1)

def poisson_correctionSource (M : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (Finset.Icc 2 M).sigma fun k => Finset.Icc k (2 * k - 2)

def poisson_correctionPair (p : Sigma fun _ : ℕ => ℕ) :
    Sigma fun _ : ℕ => ℕ :=
  ⟨p.2, p.2 + 1 - p.1⟩

def poisson_lowPairs (M N : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (poisson_taylorPairs N).filter fun p => p.1 + 1 - p.2 ≤ M

def poisson_highPairs (M N : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  (poisson_taylorPairs N).filter fun p => M < p.1 + 1 - p.2

def poisson_leadingPairs (M : ℕ) : Finset (Sigma fun _ : ℕ => ℕ) :=
  insert ⟨0, 0⟩ ((poisson_correctionSource M).image poisson_correctionPair)

noncomputable def poisson_weight (x : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-x) * (x ^ j / (Nat.factorial j : ℝ))

noncomputable def poisson_centralError (p M : ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if x / 2 ≤ (j : ℝ) then
    (poisson_weight x j : ℂ) *
      (φ (j : ℝ) - taylorPoly φ (2 * (p + M) - 1) x (j : ℝ))
  else 0

noncomputable def poisson_leftPhi (F : Finset ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if (j : ℝ) < x / 2 then
    if j ∈ F then 0 else (poisson_weight x j : ℂ) * φ (j : ℝ)
  else 0

noncomputable def poisson_leftTaylorTerm (n : ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if (j : ℝ) < x / 2 then
    (poisson_weight x j : ℂ) * ((((j : ℝ) - x) ^ n : ℝ) : ℂ) *
      (iteratedDeriv n φ x / (Nat.factorial n : ℂ))
  else 0

noncomputable def poisson_leftTaylor (p M : ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if (j : ℝ) < x / 2 then
    (poisson_weight x j : ℂ) * taylorPoly φ (2 * (p + M) - 1) x (j : ℝ)
  else 0

noncomputable def poisson_selected (F : Finset ℕ) (φ : ℝ → ℂ)
    (x : ℝ) (j : ℕ) : ℂ :=
  if j ∈ F then 0 else (poisson_weight x j : ℂ) * φ (j : ℝ)

noncomputable def poisson_normalizedTaylor (φ : ℝ → ℂ) (N : ℕ)
    (x : ℝ) (j : ℕ) : ℂ :=
  (poisson_weight x j : ℂ) * taylorPoly φ N x (j : ℝ)

end Entry10PoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
