/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfggenuinecarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgtgenuineforest.Part3
import Def.StatisticalMechanics.Code.Walls.bfggenuinecarrier
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


theorem bfg_leafSel_mem {W : Type*} (comp : W → Set (Site d)) (R : ℕ) {v : W}
    (h : (comp v ∩ vertexBoundary d R).Nonempty) :
    bfg_leafSel comp R v ∈ comp v ∩ vertexBoundary d R := by
  classical
  rw [bfg_leafSel, dif_pos h]; exact h.choose_spec


theorem bfg_leafSel_injOn {W : Type*} {S : Set W} (comp : W → Set (Site d)) (R : ℕ)
    (hne : ∀ v ∈ S, (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint (comp u) (comp v)) :
    Set.InjOn (bfg_leafSel comp R) S := by
  classical
  intro u hu v hv huv
  by_contra hne'
  have hmu : bfg_leafSel comp R u ∈ comp u := (bfg_leafSel_mem comp R (hne u hu)).1
  have hmv : bfg_leafSel comp R v ∈ comp v := (bfg_leafSel_mem comp R (hne v hv)).1
  rw [huv] at hmu
  exact Set.disjoint_left.mp (hdisj u hu v hv hne') hmu hmv


end StatMech.Walls
