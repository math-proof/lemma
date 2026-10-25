/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.blfboundaryleaf.Part3
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


theorem bau_isAcyclic_of_le_tree {V : Type*} {T G : SimpleGraph V}
    (hT : T.IsTree) (hle : G ≤ T) : G.IsAcyclic :=
  hT.isAcyclic.anti hle


theorem bau_isAcyclic_of_le_acyclic {V : Type*} {T G : SimpleGraph V}
    (hT : T.IsAcyclic) (hle : G ≤ T) : G.IsAcyclic :=
  hT.anti hle


theorem bau_exists_spanningTree_infinite {V : Type*} {H : SimpleGraph V} (hH : H.Connected) :
    ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree := by
  obtain ⟨T, hle, hT⟩ := hH.exists_isTree_le
  exact ⟨T, hle, hT⟩


theorem bau_armUnion_acyclic_of_spanningTree {V : Type*} {H G : SimpleGraph V} (hH : H.Connected)
    (T : SimpleGraph V) (hTH : T ≤ H) (hT : T.IsTree) (hle : G ≤ T) : G.IsAcyclic :=
  bau_isAcyclic_of_le_tree hT hle


end StatMech.Walls
