/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
open SimpleGraph Set Function


namespace StatMech

namespace Lattice

noncomputable def joc_cycleSubgraph {v : Site 2} (c : (hypercubicLattice 2).Walk v v)
    (_hc : c.IsCycle) : PlanarZ2Subgraph where
  V := c.toSubgraph.verts
  finV := by
    have h : c.toSubgraph.verts = {w | w ∈ c.support} := SimpleGraph.Walk.verts_toSubgraph c
    rw [h]
    exact (Set.Finite.ofFinset c.support.toFinset (by intro x; simp)).to_subtype
  decV := inferInstance
  G := c.toSubgraph.coe
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := fun x y hadj => c.toSubgraph.coe_adj_sub x y hadj


end Lattice
end StatMech
