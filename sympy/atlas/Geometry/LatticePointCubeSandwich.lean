/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Bounded cubical measure sandwich (ATLAS N385, prerequisite Stage A only)

Source: [AnalyticClassNumber.lean (lines 313--464 at
  revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L313-L464).

This module ports only the bounded cubical sandwich prerequisite: the half-open
integer unit cube, the outer and inner lattice-cube index sets, finiteness of
the outer set for bounded sets at positive scales, and the measure/cardinality
sandwich. It excludes the boundary estimate, the final asymptotic, and N386.

Declaration-to-source mapping (all within lines 313--464 above):
- `LatticePointCubeSandwich.integerUnitCube`: half-open integer unit cube.
- `LatticePointCubeSandwich.mem_integerUnitCube_iff`: unfolding lemma.
- `LatticePointCubeSandwich.outerCubeSet`: outer lattice-cube index set.
- `LatticePointCubeSandwich.mem_outerCubeSet_iff`: unfolding lemma.
- `LatticePointCubeSandwich.innerCubeSet`: inner lattice-cube index set.
- `LatticePointCubeSandwich.mem_innerCubeSet_iff`: unfolding lemma.
- `LatticePointCubeSandwich.innerCubeSet_subset_outerCubeSet`: inner indices are outer indices.
- `LatticePointCubeSandwich.finite_outerCubeSet`: finiteness of the outer set for
  bounded sets at positive scales.
- `LatticePointCubeSandwich.cube_measure_sandwich`: measure/cardinality sandwich.
-/

open MeasureTheory Set ENNReal Pointwise

namespace LatticePointCubeSandwich

/-- Half-open integer unit cube translated by `v`. -/
noncomputable def integerUnitCube {n : ℕ} (v : Fin n → ℤ) :
    Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (v i : ℝ) ((v i : ℝ) + 1))

/-- Unfolding lemma for `integerUnitCube`. -/
@[simp] theorem mem_integerUnitCube_iff {n : ℕ} {v : Fin n → ℤ}
    {x : Fin n → ℝ} :
    x ∈ integerUnitCube v ↔ ∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1 := by
  simp only [integerUnitCube, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ico]

/-- Lattice indices whose unit cube meets the scaled set. -/
def outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) :
    Set (Fin n → ℤ) :=
  {v | ∃ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S}

/-- Unfolding lemma for `outerCubeSet`. -/
@[simp] theorem mem_outerCubeSet_iff {n : ℕ} {S : Set (Fin n → ℝ)} {t : ℝ}
    {v : Fin n → ℤ} :
    v ∈ outerCubeSet S t ↔ ∃ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S :=
  Iff.rfl

/-- Lattice indices whose whole unit cube lies in the scaled set. -/
def innerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) :
    Set (Fin n → ℤ) :=
  {v | ∀ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S}

/-- Unfolding lemma for `innerCubeSet`. -/
@[simp] theorem mem_innerCubeSet_iff {n : ℕ} {S : Set (Fin n → ℝ)} {t : ℝ}
    {v : Fin n → ℤ} :
    v ∈ innerCubeSet S t ↔ ∀ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S :=
  Iff.rfl
end LatticePointCubeSandwich
