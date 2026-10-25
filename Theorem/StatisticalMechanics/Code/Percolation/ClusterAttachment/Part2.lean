/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
import Def.StatisticalMechanics.Code.Percolation.ClusterAttachment
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem cla_clusterAttachment_of_avoidingAttachment (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (h : cla_AvoidingAttachment ω x) : bma_ClusterAttachment ω x := by
  obtain ⟨a, w, hadj, hmem, hw, hri⟩ := h
  exact cla_clusterAttachment_of_avoidingWalk ω hadj hmem w hw hri


theorem cla_avoidingAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  refine ⟨x, SimpleGraph.Walk.nil, hadj, self_mem_cluster ω x, ?_, hri⟩
  simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
  exact hadj.ne


theorem cla_clusterAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x :=
  cla_clusterAttachment_of_avoidingAttachment ω x
    (cla_avoidingAttachment_of_neighbour ω x hadj hri)


end Percolation
end StatMech
