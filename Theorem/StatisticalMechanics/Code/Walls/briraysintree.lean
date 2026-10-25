/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcaconcreteclose
import Theorem.StatisticalMechanics.Code.Walls.bararmray
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bri_treeRay_of_infiniteComponent {V : Type*} [DecidableEq V] (T : SimpleGraph V)
    [LocallyFinite T] {w : V} (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → V, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) := by
  obtain ⟨r, hr0, hinj, hadj, -⟩ := ray34_konig T (Set.notMem_empty w) hinf
  exact ⟨r, hr0, hinj, hadj⟩


theorem bri_branchRay_avoiding_vertex {V : Type*} [DecidableEq V] (T : SimpleGraph V)
    [LocallyFinite T] {w x : V} (hwx : w ≠ x)
    (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → V, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) := by
  have hw : w ∉ ({x} : Set V) := by simpa using hwx
  obtain ⟨r, hr0, hinj, hadj, havoid⟩ := ray34_konig T hw hinf
  exact ⟨r, hr0, hinj, hadj, fun k => by have := havoid k; simpa using this⟩


theorem bri_treeRay_reaches_boundary (T : SimpleGraph (Site d)) [LocallyFinite T]
    (hle : T ≤ hypercubicLattice d) {w : Site d} {R : ℕ} (hR : 1 ≤ R) (hw : w ∈ box d R)
    (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
  obtain ⟨r, hr0, hinj, hadj⟩ := bri_treeRay_of_infiniteComponent T hinf
  have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k => hle (hadj k)
  have h0box : r 0 ∈ box d R := by rw [hr0]; exact hw
  obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
  exact ⟨r, hr0, hinj, hadj, ⟨k, hk⟩⟩


theorem bri_branchRay_reaches_boundary (T : SimpleGraph (Site d)) [LocallyFinite T]
    (hle : T ≤ hypercubicLattice d) {w x : Site d} {R : ℕ} (hR : 1 ≤ R) (hwx : w ≠ x)
    (hw : w ∈ box d R) (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
    ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
  obtain ⟨r, hr0, hinj, hadj, havoid⟩ := bri_branchRay_avoiding_vertex T hwx hinf
  have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k => hle (hadj k)
  have h0box : r 0 ∈ box d R := by rw [hr0]; exact hw
  obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
  exact ⟨r, hr0, hinj, hadj, havoid, ⟨k, hk⟩⟩

#check @bri_treeRay_reaches_boundary
#check @bri_branchRay_reaches_boundary


end StatMech.Walls
