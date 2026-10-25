/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Def.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem lma_boxAttachData_of_reachesRay {n : ℕ}
    (h : lma_BoxClusterReachesRay d n) : tex_BoxAttachData d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, h1, h2, h3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3


theorem lma_disjointRouting_of_reachesRay {n : ℕ}
    (h : lma_BoxClusterReachesRay d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box (lma_boxAttachData_of_reachesRay h)


theorem lma_clusterReachesRay_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay ω (hrHD_rayPt j 1) j := by
  refine ⟨0, self_mem_cluster ω (hrHD_rayPt j 1), ?_, ?_, hinf⟩
  · rw [lma_corridorEdges_zero]; intro e he; exact absurd he (Finset.notMem_empty e)
  · simpa using connected_rfl


theorem lma_attachData_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
    (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
    tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) :=
  lma_attachData_of_three_reachesRay ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)
    j₁ j₂ j₃ hcd12 hcd13 hcd23
    (lma_clusterReachesRay_of_neighbour ω j₁ hi1)
    (lma_clusterReachesRay_of_neighbour ω j₂ hi2)
    (lma_clusterReachesRay_of_neighbour ω j₃ hi3)


theorem lma_corridorVerts_nonempty (j : Fin d) (L : ℕ) :
    (lma_corridorVerts j L).Nonempty :=
  ⟨hrHD_rayPt j 1, 1, le_rfl, by omega, by norm_num⟩

end Percolation
end StatMech
