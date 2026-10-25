/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Def.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part2
open Filter Finset Topology


namespace StatMech.FrontierA

@[simp] theorem randomWalkPartial_zero {X : Type*}
    (T : PositiveAdditiveOperator X) (delta : X → ℝ) :
    randomWalkPartial T delta 0 = 0 := rfl

@[simp] theorem randomWalkPartial_succ {X : Type*}
    (T : PositiveAdditiveOperator X) (delta : X → ℝ) (n : ℕ) :
    randomWalkPartial T delta (n + 1) =
      delta + T (randomWalkPartial T delta n) := rfl


theorem randomWalkPartial_succ_eq_add_iterate {X : Type*}
    (T : PositiveAdditiveOperator X) (delta : X → ℝ) (n : ℕ) :
    randomWalkPartial T delta (n + 1) =
      randomWalkPartial T delta n + randomWalkIterate T n delta := by
  induction n with
  | zero =>
      rw [randomWalkPartial_succ, randomWalkPartial_zero, T.map_zero,
        randomWalkIterate_zero]
      simp
  | succ n ih =>
      calc
        randomWalkPartial T delta (n + 1 + 1) =
            delta + T (randomWalkPartial T delta (n + 1)) := rfl
        _ = delta + T (randomWalkPartial T delta n +
            randomWalkIterate T n delta) := by rw [ih]
        _ = (delta + T (randomWalkPartial T delta n)) +
            T (randomWalkIterate T n delta) := by rw [T.map_add]; abel
        _ = randomWalkPartial T delta (n + 1) +
            randomWalkIterate T (n + 1) delta := rfl


theorem randomWalkPartial_eq_sum_iterates {X : Type*}
    (T : PositiveAdditiveOperator X) (delta : X → ℝ) (n : ℕ) :
    randomWalkPartial T delta n =
      ∑ k ∈ Finset.range n, randomWalkIterate T k delta := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [randomWalkPartial_succ_eq_add_iterate, ih, Finset.sum_range_succ]


theorem randomWalkIterate_nonneg {X : Type*}
    (T : PositiveAdditiveOperator X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∀ n x, 0 ≤ randomWalkIterate T n f x := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih =>
      intro x
      rw [randomWalkIterate_succ]
      calc
        0 = T (0 : X → ℝ) x := by rw [T.map_zero]; rfl
        _ ≤ T (randomWalkIterate T n f) x := (T.monotone ih) x


theorem randomWalkPartial_nonneg {X : Type*}
    (T : PositiveAdditiveOperator X) (delta : X → ℝ)
    (hdelta : ∀ x, 0 ≤ delta x) :
    ∀ n x, 0 ≤ randomWalkPartial T delta n x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro x
      rw [randomWalkPartial_succ, Pi.add_apply]
      exact add_nonneg (hdelta x)
        (randomWalkIterate_nonneg T (randomWalkPartial T delta n) ih 1 x)


theorem renewal_le_partial_add_remainder {X : Type*}
    (T : PositiveAdditiveOperator X) (delta twoPoint : X → ℝ)
    (hrenewal : ∀ x, twoPoint x ≤ delta x + T twoPoint x) :
    ∀ n x, twoPoint x ≤
      randomWalkPartial T delta n x + randomWalkIterate T n twoPoint x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      have hmonotone : T twoPoint ≤
          T (randomWalkPartial T delta n + randomWalkIterate T n twoPoint) :=
        T.monotone ih
      intro x
      calc
        twoPoint x ≤ delta x + T twoPoint x := hrenewal x
        _ ≤ delta x +
            T (randomWalkPartial T delta n + randomWalkIterate T n twoPoint) x :=
          by linarith [hmonotone x]
        _ = randomWalkPartial T delta (n + 1) x +
            randomWalkIterate T (n + 1) twoPoint x := by
          rw [T.map_add]
          simp only [randomWalkPartial_succ, randomWalkIterate_succ, Pi.add_apply]
          ring


theorem renewal_le_effectiveRandomWalk {X : Type*}
    (T : PositiveAdditiveOperator X) (delta twoPoint green : X → ℝ)
    (hrenewal : ∀ x, twoPoint x ≤ delta x + T twoPoint x)
    (hpartial : ∀ x, Tendsto (fun n => randomWalkPartial T delta n x)
      atTop (nhds (green x)))
    (hremainder : ∀ x, Tendsto (fun n => randomWalkIterate T n twoPoint x)
      atTop (nhds 0)) :
    ∀ x, twoPoint x ≤ green x := by
  intro x
  have hsum : Tendsto
      (fun n => randomWalkPartial T delta n x +
        randomWalkIterate T n twoPoint x) atTop (nhds (green x + 0)) :=
    (hpartial x).add (hremainder x)
  exact ge_of_tendsto (by simpa using hsum) (Eventually.of_forall (fun n =>
    renewal_le_partial_add_remainder T delta twoPoint hrenewal n x))


end StatMech.FrontierA
