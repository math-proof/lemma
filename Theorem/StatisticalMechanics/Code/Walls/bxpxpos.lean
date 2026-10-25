/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bmfmergefree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


variable {d : ℕ}


theorem bxp_cluster_removeSite_eq (ω : ConfigSpace (Sym2 (Site d))) {b : Site d}
    (h0 : (0 : Site d) ∉ cluster d ω b) :
    cluster d (removeSite 0 ω) b = cluster d ω b := by
  apply Set.Subset.antisymm
  · exact cluster_mono (removeSite_le 0 ω) b
  · intro y hy
    have hcon : Connected d ω b y := mem_cluster.mp hy
    obtain ⟨p⟩ := hcon
    have hcl : cluster d ω b = cluster d ω y := cluster_eq_of_connected (mem_cluster.mp hy)
    have h0y : (0 : Site d) ∉ cluster d ω y := hcl ▸ h0
    have h0p : (0 : Site d) ∉ p.support :=
      ava_origin_notMem_support_of_notMem_cluster ω p h0y
    exact mem_cluster.mpr (pap_connected_removeSite_of_walk_avoid ω 0 p h0p)


theorem bxp_infinite_removeSite (ω : ConfigSpace (Sym2 (Site d))) {b : Site d}
    (h0 : (0 : Site d) ∉ cluster d ω b) (hinf : (cluster d ω b).Infinite) :
    (cluster d (removeSite 0 ω) b).Infinite := by
  rw [bxp_cluster_removeSite_eq ω h0]; exact hinf


theorem bxp_notConnected_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a b : Site d}
    (h : ¬ Connected d ω a b) : ¬ Connected d (removeSite 0 ω) a b :=
  fun hc => h (ava_connected_of_removeSite ω hc)


end StatMech.Walls
