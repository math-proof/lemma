/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Def.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tex_boxMengerAttachment_of_boxAttachData {n : ℕ}
    (h : tex_BoxAttachData d n) : bmm_BoxMengerAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23


theorem tex_threeClustersReachOrigin_of_box {n : ℕ}
    (h : tex_BoxAttachData d n) :
    ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  bmm_threeClustersReachOrigin_of_attachment (tex_boxMengerAttachment_of_boxAttachData h)


theorem tex_disjointRouting_of_box {n : ℕ}
    (h : tex_BoxAttachData d n) : hrHD_DisjointRouting d n :=
  bmm_disjointRouting_of_attachment (tex_boxMengerAttachment_of_boxAttachData h)


theorem tex_attachData_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    tex_AttachData ω x₁ x₂ x₃ := by
  classical
  refine ⟨x₁, x₂, x₃, ∅, hadj, ?_, ?_, ?_, ?_, hri⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · exact ⟨self_mem_cluster ω x₁, self_mem_cluster ω x₂, self_mem_cluster ω x₃⟩
  · refine ⟨?_, ?_, ?_⟩ <;> (intro u v _ hW; exact absurd hW (Finset.notMem_empty _))
  · exact ⟨connected_rfl, connected_rfl, connected_rfl⟩


theorem tex_threeClustersReachOrigin_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ hd
    (tex_attachData_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri)


theorem tex_boxAttachData_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    tex_AttachData ω x₁ x₂ x₃ :=
  tex_attachData_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri

end Percolation
end StatMech
