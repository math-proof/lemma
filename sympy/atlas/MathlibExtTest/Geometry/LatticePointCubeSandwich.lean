/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/LatticePointCubeSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.Geometry.LatticePointCubeSandwich
import Lemma.Set.LatticePointCubeSandwich

/-!
# Tests for the bounded cubical measure sandwich

Concrete checks for `LatticePointCubeSandwich`:

- The half-open unit interval at `t = 1` meets the outer cube `0` but not
  cube `1`, and cube `0` is also inner.
- Direct uses of the inclusion, finiteness, and sandwich API on abstract
  bounded sets.
- The `n = 0` edge case.
-/

open LatticePointCubeSandwich MeasureTheory

/-- The half-open unit interval as a `Fin 1` box. -/
noncomputable def halfOpenUnit : Set (Fin 1 → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)

/-- The origin lies in its own half-open integer unit cube. -/
example : (fun _ => (0 : ℝ)) ∈
    integerUnitCube (n := 1) (fun _ => (0 : ℤ)) := by
  rw [mem_integerUnitCube_iff]
  intro i
  simp

/-- At `t = 1`, cube `0` meets the half-open unit interval. -/
example : (fun _ => (0 : ℤ)) ∈ outerCubeSet halfOpenUnit 1 := by
  rw [mem_outerCubeSet_iff]
  refine ⟨fun _ => 0, ?_, ?_⟩
  · rw [mem_integerUnitCube_iff]
    intro i
    simp
  · simp only [halfOpenUnit, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Ico]
    intro i
    simp

/-- At `t = 1`, cube `1` misses the half-open unit interval. -/
example : (fun _ => (1 : ℤ)) ∉ outerCubeSet halfOpenUnit 1 := by
  intro h
  rw [mem_outerCubeSet_iff] at h
  obtain ⟨x, hxv, hxS⟩ := h
  rw [mem_integerUnitCube_iff] at hxv
  simp only [halfOpenUnit, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ico] at hxS
  have h1 := (hxv 0).1
  have h2 : x 0 / (1 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := hxS 0
  rw [Set.mem_Ico] at h2
  simp only [Int.cast_one] at h1
  linarith [h2.2]

/-- At `t = 1`, cube `0` is fully inside the half-open unit interval. -/
example : (fun _ => (0 : ℤ)) ∈ innerCubeSet halfOpenUnit 1 := by
  rw [mem_innerCubeSet_iff]
  intro x hxv
  rw [mem_integerUnitCube_iff] at hxv
  simp only [halfOpenUnit, Set.mem_pi, Set.mem_univ, true_implies] at ⊢
  intro i
  have h := hxv i
  simp only [Set.mem_Ico] at h ⊢
  simp only [Int.cast_zero, zero_add, div_one] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- Generic use of the inner/outer inclusion. -/
example {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) :
    innerCubeSet S t ⊆ outerCubeSet S t :=
  innerCubeSet_subset_outerCubeSet S t

/-- Generic use of outer-set finiteness. -/
example {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Bornology.IsBounded S)
    {t : ℝ} (ht : 0 < t) : (outerCubeSet S t).Finite :=
  finite_outerCubeSet S hS ht

/-- Generic use of the left sandwich inequality. -/
example {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Bornology.IsBounded S)
    {t : ℝ} (ht : 0 < t) :
    (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n :=
  (cube_measure_sandwich S hS ht).1

/-- Generic use of the right sandwich inequality. -/
example {n : ℕ} (S : Set (Fin n → ℝ)) (hS : Bornology.IsBounded S)
    {t : ℝ} (ht : 0 < t) :
    (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) :=
  (cube_measure_sandwich S hS ht).2

/-- The `n = 0` outer set is finite. -/
example : ((outerCubeSet ({0} : Set (Fin 0 → ℝ)) 2).Finite) :=
  finite_outerCubeSet _ singleton_zero_bounded (by norm_num)

/-- The `n = 0` sandwich applies. -/
example : (Nat.card (innerCubeSet ({0} : Set (Fin 0 → ℝ)) 2) : ℝ) ≤
    (volume ({0} : Set (Fin 0 → ℝ))).toReal * (2 : ℝ) ^ 0 ∧
    (volume ({0} : Set (Fin 0 → ℝ))).toReal * (2 : ℝ) ^ 0 ≤
    (Nat.card (outerCubeSet ({0} : Set (Fin 0 → ℝ)) 2) : ℝ) :=
  cube_measure_sandwich _ singleton_zero_bounded (by norm_num)
