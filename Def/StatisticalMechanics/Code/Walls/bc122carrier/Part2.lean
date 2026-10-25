/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier
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


def bc122_HubBoundaryArms (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) : Prop :=
  
  (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧
  
  (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ∀ j k, arm y j = arm z k → y = z ∧ j = k) ∧
  
  (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ∀ j, arm y j ≠ z)


open Classical in

noncomputable def bc122_hubs (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Finset (Site d) := by
  classical
  exact (boxFinsetBK d R).filter (fun y => bc67_IsGnTrifurcation ω L y)

end StatMech.Walls
