/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Def.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bma_boxMengerAttachment {n : ℕ}
    (h : bma_BoxClusterAttachment d n) : bmm_BoxMengerAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨ha1, ha2, ha3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact bma_attachment_of_three_clusterAttachments ω x₁ x₂ x₃ hcd12 hcd13 hcd23 ha1 ha2 ha3


theorem bma_boxMergeFreeInsertion_of_clusterAttachment {n : ℕ}
    (h : bma_BoxClusterAttachment d n) : tre_BoxMergeFreeInsertion d n :=
  bmm_boxMergeFreeInsertion_of_attachment (bma_boxMengerAttachment h)


theorem bma_disjointRouting_of_clusterAttachment {n : ℕ}
    (h : bma_BoxClusterAttachment d n) : hrHD_DisjointRouting d n :=
  bmm_disjointRouting_of_attachment (bma_boxMengerAttachment h)


theorem bma_clusterAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x := by
  classical
  refine ⟨x, ∅, hadj, ?_, ?_, self_mem_cluster ω x, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact connected_rfl


theorem bma_three_clusterAttachments_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    bma_ClusterAttachment ω x₁ ∧ bma_ClusterAttachment ω x₂ ∧ bma_ClusterAttachment ω x₃ :=
  ⟨bma_clusterAttachment_of_neighbour ω x₁ hadj.1 hri.1,
    bma_clusterAttachment_of_neighbour ω x₂ hadj.2.1 hri.2.1,
    bma_clusterAttachment_of_neighbour ω x₃ hadj.2.2 hri.2.2⟩

end Percolation
end StatMech
