/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevDerivatives
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.FourierInversion
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Mathlib.Algebra.MvPolynomial.Degrees

open scoped SchwartzMap ContDiff FourierTransform
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory

noncomputable section

namespace DiffOpSobolev

variable (n : ℕ)

/-- A tempered distribution `u` lies in the Sobolev space `H^m` if it is represented
by integration against an element of `SobolevSpace n m`. -/
def IsInSobolev (m : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ f : SobolevSpace n m,
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      u φ = ∫ x : EuclideanSpace ℝ (Fin n), φ x • f x


/-- Action of a constant-coefficient differential operator `P(D)` on a distribution
represented by a Sobolev `H^s` function: the result is represented by an `H^{s-k}`
function, when the polynomial has degree at most `k ≤ s`. -/
class `H^s` into `H^{s-k}` (Melrose, Section 10, Prop 10.2). -/
def tailMultiIndexSum {n : ℕ} (α : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun j : Fin n => k ≤ j.val), α i

/-- If `k ≥ n`, the tail sum `∑_{i ≥ k} α i` is empty and hence `0`. -/
lemma tailMultiIndexSum_ge {n : ℕ} (α : Fin n → ℕ) (k : ℕ) (hk : n ≤ k) :
    tailMultiIndexSum α k = 0 := by
  simp only [tailMultiIndexSum]
  apply Finset.sum_eq_zero
  intro i hi
  simp [Finset.mem_filter] at hi
  omega

/-- Recurrence for the tail sum: peel off the term at index `k`. -/
lemma tailMultiIndexSum_succ {n : ℕ} (α : Fin n → ℕ) (k : ℕ) (hk : k < n) :
    tailMultiIndexSum α k = α ⟨k, hk⟩ + tailMultiIndexSum α (k + 1) := by
  simp only [tailMultiIndexSum]
  have hsplit : Finset.univ.filter (fun j : Fin n => k ≤ j.val) =
      {⟨k, hk⟩} ∪ Finset.univ.filter (fun j : Fin n => k + 1 ≤ j.val) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton]
    constructor
    · intro hx
      by_cases hxk : x.val = k
      · left; exact Fin.ext hxk
      · right; omega
    · intro hx
      rcases hx with hx | hx
      · subst hx; simp
      · omega
  rw [hsplit, Finset.sum_union]
  · simp
  · rw [Finset.disjoint_singleton_left]
    simp [Finset.mem_filter]

/-- Auxiliary recursion computing the multi-index iterated partial derivative on
`SobolevSpace n m'` by processing coordinates starting at index `k`. -/
def multiIndexDerivGo {n : ℕ} (α : Fin n → ℕ)
    (k : ℕ) (m' : ℕ) (hsum : tailMultiIndexSum α k ≤ m')
    (u : SobolevSpace n m') : SobolevSpace n (m' - tailMultiIndexSum α k) :=
  if hk : k < n then
    have hαk : α ⟨k, hk⟩ ≤ m' := by
      have := tailMultiIndexSum_succ α k hk
      omega
    let v := SobolevSpace.iteratedPartialDeriv ⟨k, hk⟩ (α ⟨k, hk⟩) hαk u
    have hsum' : tailMultiIndexSum α (k + 1) ≤ m' - α ⟨k, hk⟩ := by
      have := tailMultiIndexSum_succ α k hk
      omega
    have heq : m' - α ⟨k, hk⟩ - tailMultiIndexSum α (k + 1) =
        m' - tailMultiIndexSum α k := by
      have := tailMultiIndexSum_succ α k hk
      omega
    heq ▸ multiIndexDerivGo α (k + 1) (m' - α ⟨k, hk⟩) hsum' v
  else
    have heq : tailMultiIndexSum α k = 0 := tailMultiIndexSum_ge α k (by omega)
    heq ▸ u
  termination_by n - k

/-- The monomial `x^α := ∏ x_i^{α_i}` viewed as a multivariate polynomial. -/
def multiIndexMonomial (α : Fin n → ℕ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) 1
