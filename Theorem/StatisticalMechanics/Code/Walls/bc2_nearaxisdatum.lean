/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Def.StatisticalMechanics.Code.Walls.bc2_nearaxisdatum
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc2_nearAxis_mem (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} {j : Fin d}
    (h : bc2_NearAxis ω x j) : hrHD_rayPt j 1 ∈ cluster d ω x := h.1


theorem bc2_nearAxis_connected (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} {j : Fin d}
    (h : bc2_NearAxis ω x j) : Connected d (removeSite 0 ω) (hrHD_rayPt j 1) x := h.2.1


theorem bc2_nearAxis_infinite (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} {j : Fin d}
    (h : bc2_NearAxis ω x j) : (cluster d (removeSite 0 ω) x).Infinite := h.2.2


theorem bc2_clusterReachesRay_of_nearAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc2_NearAxis ω x j) : lma_ClusterReachesRay ω x j := by
  obtain ⟨hmem, hreach, hinf⟩ := h
  refine ⟨0, hmem, ?_, ?_, hinf⟩
  · intro e he
    rw [lma_corridorEdges_zero] at he
    exact absurd he (Finset.notMem_empty e)
  · have he : ((0 : ℕ) : ℤ) + 1 = (1 : ℤ) := by norm_num
    rw [he]
    exact hreach


theorem bc2_attachData_of_three_nearAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : bc2_NearAxis ω x₁ j₁) (h2 : bc2_NearAxis ω x₂ j₂) (h3 : bc2_NearAxis ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ :=
  lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23
    (bc2_clusterReachesRay_of_nearAxis ω x₁ j₁ h1)
    (bc2_clusterReachesRay_of_nearAxis ω x₂ j₂ h2)
    (bc2_clusterReachesRay_of_nearAxis ω x₃ j₃ h3)


theorem bc2_threeClustersReachOrigin_of_three_nearAxis (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : bc2_NearAxis ω x₁ j₁) (h2 : bc2_NearAxis ω x₂ j₂) (h3 : bc2_NearAxis ω x₃ j₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ ⟨hcd12, hcd13, hcd23⟩
    (bc2_attachData_of_three_nearAxis ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3)


end Walls
end StatMech
