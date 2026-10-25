/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterAttachment.Part3
import Def.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem ava_boxAvoidingAttachment_of_boxResidue {n : ℕ}
    (h : ava_BoxAvoidingRoutingResidue d n) : cla_BoxAvoidingAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨h1, h2, h3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨ava_avoidingAttachment ω x₁ h1, ava_avoidingAttachment ω x₂ h2,
    ava_avoidingAttachment ω x₃ h3⟩


theorem ava_disjointRouting_of_boxResidue {n : ℕ}
    (h : ava_BoxAvoidingRoutingResidue d n) : hrHD_DisjointRouting d n :=
  cla_disjointRouting_of_boxAvoiding (ava_boxAvoidingAttachment_of_boxResidue h)


theorem ava_three_residues_of_neighbours (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧
      ava_AvoidingRoutingResidue ω x₃ :=
  ⟨ava_avoidingRoutingResidue_of_neighbour ω x₁ hadj.1 hri.1,
    ava_avoidingRoutingResidue_of_neighbour ω x₂ hadj.2.1 hri.2.1,
    ava_avoidingRoutingResidue_of_neighbour ω x₃ hadj.2.2 hri.2.2⟩

end Percolation
end StatMech
