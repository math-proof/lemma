/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LovaszSimonovits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.Cheeger
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Cheeger

namespace LovaszSimonovits

noncomputable def sortedValues {n : ℕ} (ρ : Fin n → ℝ) : Fin n → ℝ := by
  classical
  let vals : List ℝ := ((List.finRange n).map ρ).mergeSort (· ≥ ·)
  exact fun i => vals.getD i.val 0

noncomputable def partialSum {n : ℕ} (w : Fin n → ℝ) (k : ℕ) : ℝ :=
  Finset.univ.sum (fun i : Fin n => if i.val < k then w i else 0)

noncomputable def lsCurve {n : ℕ} (ρ : Fin n → ℝ) (x : ℝ) : ℝ :=
  if n = 0 then 0
  else
    let w := sortedValues ρ
    let k := Nat.floor x
    if h : k ≥ n then partialSum w n
    else partialSum w k + (x - ↑k) * w ⟨k, by omega⟩

def IsSortedDecreasing {n : ℕ} (w : Fin n → ℝ) : Prop :=
  Antitone w

def LSCurveIsConcave {n : ℕ} (ρ : Fin n → ℝ) : Prop :=
  IsSortedDecreasing (sortedValues ρ)

def WeightedSumInequality {n : ℕ} (ρ : Fin n → ℝ) : Prop :=
  ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → (∀ i, c i ≤ 1) →
    Finset.univ.sum (fun i => c i * sortedValues ρ i) ≤
      lsCurve ρ (Finset.univ.sum c)

def RandomWalkStepReal {n : ℕ} (ρ_prev ρ_curr : Fin n → ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ ↑n →
    ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ i, c i ≤ 1) ∧
      (Finset.univ.sum c = x) ∧
      lsCurve ρ_curr x =
        Finset.univ.sum (fun i => c i * sortedValues ρ_prev i)

noncomputable def lovaszSimonovitsBound (n : ℕ) (φ : ℝ) (t : ℕ) (x : ℝ) : ℝ :=
  min (Real.sqrt x) (Real.sqrt (↑n - x)) * (1 - φ^2 / 2)^t + x / ↑n

def SatisfiesEvolutionBound {n : ℕ} (ρ : ℕ → Fin n → ℝ) (φ : ℝ) : Prop :=
  ∀ t : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ ↑n →
    lsCurve (ρ (t + 1)) x ≤
      if x ≤ ↑n / 2 then
        (1/2) * (lsCurve (ρ t) (x - 2 * φ * x) + lsCurve (ρ t) (x + 2 * φ * x))
      else
        (1/2) * (lsCurve (ρ t) (x - 2 * φ * (↑n - x)) +
                 lsCurve (ρ t) (x + 2 * φ * (↑n - x)))

def MidpointBoundLower (n : ℕ) (φ : ℝ) : Prop :=
  ∀ t : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ ↑n / 2 →
    (1/2) * (lovaszSimonovitsBound n φ t (x - 2 * φ * x) +
             lovaszSimonovitsBound n φ t (x + 2 * φ * x)) ≤
      lovaszSimonovitsBound n φ (t + 1) x

def MidpointBoundUpper (n : ℕ) (φ : ℝ) : Prop :=
  ∀ t : ℕ, ∀ x : ℝ, ↑n / 2 ≤ x → x ≤ ↑n →
    (1/2) * (lovaszSimonovitsBound n φ t (x - 2 * φ * (↑n - x)) +
             lovaszSimonovitsBound n φ t (x + 2 * φ * (↑n - x))) ≤
      lovaszSimonovitsBound n φ (t + 1) x
