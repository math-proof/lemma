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
import Def.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem lma_clusterAttachment_of_reachesRay (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : lma_ClusterReachesRay ω x j) :
    bma_ClusterAttachment ω x := by
  obtain ⟨L, he1, hin, hreach, hinf⟩ := h
  refine ⟨hrHD_rayPt j 1, lma_corridorEdges j L, hrHD_adj_origin_rayPt_one j,
    lma_origin_notMem_corridorEdges j L, hin, he1, ?_, hinf⟩
  have hcorr : Connected d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := lma_corridor_connected ω j L L le_rfl
  have htail : Connected d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j ((L : ℤ) + 1)) x :=
    connected_mono (lma_removeSite_le_forceOpen ω (lma_corridorEdges j L)) hreach
  exact hcorr.trans htail


theorem lma_attachData_of_three_reachesRay (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : lma_ClusterReachesRay ω x₁ j₁) (h2 : lma_ClusterReachesRay ω x₂ j₂)
    (h3 : lma_ClusterReachesRay ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ :=
  bma_attachment_of_three_clusterAttachments ω x₁ x₂ x₃ hcd12 hcd13 hcd23
    (lma_clusterAttachment_of_reachesRay ω x₁ j₁ h1)
    (lma_clusterAttachment_of_reachesRay ω x₂ j₂ h2)
    (lma_clusterAttachment_of_reachesRay ω x₃ j₃ h3)


theorem lma_threeClustersReachOrigin_of_three_reachesRay (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : lma_ClusterReachesRay ω x₁ j₁) (h2 : lma_ClusterReachesRay ω x₂ j₂)
    (h3 : lma_ClusterReachesRay ω x₃ j₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ ⟨hcd12, hcd13, hcd23⟩
    (lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3)


end Percolation
end StatMech
