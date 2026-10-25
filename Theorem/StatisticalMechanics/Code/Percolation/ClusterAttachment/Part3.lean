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
import Def.StatisticalMechanics.Code.Percolation.ClusterAttachment.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem cla_boxClusterAttachment_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : bma_BoxClusterAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨ha1, ha2, ha3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨cla_clusterAttachment_of_avoidingAttachment ω x₁ ha1,
    cla_clusterAttachment_of_avoidingAttachment ω x₂ ha2,
    cla_clusterAttachment_of_avoidingAttachment ω x₃ ha3⟩


theorem cla_boxMengerAttachment_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : bmm_BoxMengerAttachment d n :=
  bma_boxMengerAttachment (cla_boxClusterAttachment_of_boxAvoiding h)


theorem cla_disjointRouting_of_boxAvoiding {n : ℕ}
    (h : cla_BoxAvoidingAttachment d n) : hrHD_DisjointRouting d n :=
  bma_disjointRouting_of_clusterAttachment (cla_boxClusterAttachment_of_boxAvoiding h)


theorem cla_three_avoidingAttachments_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    cla_AvoidingAttachment ω x₁ ∧ cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃ :=
  ⟨cla_avoidingAttachment_of_neighbour ω x₁ hadj.1 hri.1,
    cla_avoidingAttachment_of_neighbour ω x₂ hadj.2.1 hri.2.1,
    cla_avoidingAttachment_of_neighbour ω x₃ hadj.2.2 hri.2.2⟩

end Percolation
end StatMech
