/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped BigOperators

/-- A generic nonnegative discrete spectrum: a zero-based eigenvalue sequence,
counted with multiplicity by index, diverging to `+∞`.

This is a transform layer only. It does not claim that an arbitrary sequence
is a Dirichlet or Neumann Laplacian spectrum; connecting a sequence to an
operator is left to a later domain-specific construction. -/
structure NonnegativeDiscreteSpectrum where
  eigenvalue : ℕ → ℝ
  nonnegative_eigenvalue : ∀ j, 0 ≤ eigenvalue j
  monotone_eigenvalue : Monotone eigenvalue
  tendsto_eigenvalue_atTop :
    Filter.Tendsto eigenvalue Filter.atTop Filter.atTop

namespace NonnegativeDiscreteSpectrum

instance : CoeFun NonnegativeDiscreteSpectrum (fun _ => ℕ → ℝ) :=
  ⟨NonnegativeDiscreteSpectrum.eigenvalue⟩

/-- Pointwise extensionality: spectra with equal eigenvalue functions are equal;
proof fields are irrelevant. -/
@[ext] theorem ext {S T : NonnegativeDiscreteSpectrum} (h : ∀ j, S j = T j) :
    S = T := by
  obtain ⟨eS, h1S, h2S, h3S⟩ := S
  obtain ⟨eT, h1T, h2T, h3T⟩ := T
  have he : eS = eT := funext h
  subst he
  rfl

/-- Strict sublevel set: indices with eigenvalue strictly below the cutoff.
The strict inequality encodes the standard convention `(Λ - E_j)_+^0 = 1`
only when `E_j < Λ`, avoiding `0 ^ 0 = 1` at the cutoff. -/
def sublevelSet (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : Set ℕ :=
  {j | S j < Λ}

/-- The strict sublevel set is finite: monotonicity plus divergence to `+∞`
bounds it by an initial segment. -/
theorem sublevelSet_finite
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) :
    (S.sublevelSet Λ).Finite := by
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp S.tendsto_eigenvalue_atTop Λ
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range N)) fun j hj => ?_
  simp only [sublevelSet, Set.mem_ofPred_eq] at hj
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have hle : N ≤ j := not_lt.mp h
  exact (not_le.mpr hj) (hN j hle)

/-- The strict sublevel set as a finset. -/
noncomputable def sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : Finset ℕ :=
  (S.sublevelSet_finite Λ).toFinset

/-- Exact membership for the sublevel finset. -/
@[simp] theorem mem_sublevelFinset
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) (j : ℕ) :
    j ∈ S.sublevelFinset Λ ↔ S j < Λ := by
  rw [sublevelFinset, Set.Finite.mem_toFinset]
  rfl

/-- Strict counting function `N(Λ) = #{j | E_j < Λ}`, with multiplicity. -/
noncomputable def countingFunction
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : ℕ :=
  (S.sublevelFinset Λ).card

/-- Finite Riesz mean `R_σ(Λ) = ∑_{E_j < Λ} (Λ - E_j)^σ` via `Real.rpow`. -/
noncomputable def rieszMean
    (S : NonnegativeDiscreteSpectrum) (σ Λ : ℝ) : ℝ :=
  ∑ j ∈ S.sublevelFinset Λ, Real.rpow (Λ - S j) σ

/-- The `σ = 0` endpoint recovers the counting function, since every
summand has strictly positive base. -/
@[simp] theorem rieszMean_zero
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) :
    S.rieszMean 0 Λ = S.countingFunction Λ := by
  simp [rieszMean, countingFunction]

end NonnegativeDiscreteSpectrum
