/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory ProbabilityTheory Finset Set

noncomputable section

/-- The partial sum `Sₖ(ω) = ∑_{i ≤ k} Xᵢ(ω)` of a finite family of random variables. -/
def partialSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (k : Fin n) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Iic k, X i ω

/-- The "first crossing at time `k`" event: the set of `ω` for which `|Sₖ(ω)| ≥ ε` but
`|Sⱼ(ω)| < ε` for every `j < k`. These events partition `{∃ k, |Sₖ| ≥ ε}` into disjoint
pieces and are the standard tool in the proof of Kolmogorov's maximal inequality. -/
def stoppingEvent {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ) (k : Fin n) : Set Ω :=
  {ω | |partialSum X k ω| ≥ ε ∧ ∀ j : Fin n, j < k → |partialSum X j ω| < ε}

/-- The full sum `Sₙ(ω) = ∑_{i : Fin n} Xᵢ(ω)` of the family `X`. -/
def fullSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, X i ω

/-- The tail sum `∑_{i > k} Xᵢ(ω)` after index `k`. -/
def tailSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (k : Fin n) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Ioi k, X i ω

/-- The "abstract" partial sum: given a vector `v` indexed by `Finset.Iic k`, sum its
components at indices `≤ j`. Used to express `Sⱼ` as a function of `(Xᵢ)_{i ≤ k}` for
independence arguments. -/
def piPartialSum' {n : ℕ} (k : Fin n) (v : ↥(Finset.Iic k) → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun (x : ↥(Finset.Iic k)) => (x : Fin n) ≤ j), v i

/-- The "abstract" version of `stoppingEvent` as a subset of `↥(Finset.Iic k) → ℝ`. -/
def piStoppingSet {n : ℕ} (ε : ℝ) (k : Fin n) : Set (↥(Finset.Iic k) → ℝ) :=
  {v | |piPartialSum' k v k| ≥ ε ∧ ∀ j : Fin n, j < k → |piPartialSum' k v j| < ε}

/-- The function `Φ` on `↥(Finset.Iic k) → ℝ` that takes value `Sₖ(v)` on the stopping set
and `0` outside it. When composed with `ω ↦ (Xᵢ(ω))_{i ≤ k}` it recovers the
indicator-weighted partial sum `1_{stoppingEvent} · Sₖ`. -/
def piPhi' {n : ℕ} (ε : ℝ) (k : Fin n) : (↥(Finset.Iic k) → ℝ) → ℝ :=
  (piStoppingSet ε k).indicator (fun v => piPartialSum' k v k)

/-- The function `Ψ` on `↥(Finset.Ioi k) → ℝ` summing all coordinates; composed with
`ω ↦ (Xᵢ(ω))_{i > k}` it gives the tail sum `Sₙ - Sₖ`. -/
def piPsi' {n : ℕ} (k : Fin n) (v : ↥(Finset.Ioi k) → ℝ) : ℝ :=
  ∑ i : ↥(Finset.Ioi k), v i
