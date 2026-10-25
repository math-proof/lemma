/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.AxisAssignmentClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationFiniteEnergy.Part3
open MeasureTheory Set Finset
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem lmg_corridors_disjoint {j₁ j₂ j₃ : Fin d}
    (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃) (L : ℕ) :
    (Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) ∧
      Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₃ L) ∧
      Disjoint (lma_corridorVerts j₂ L) (lma_corridorVerts j₃ L)) ∧
    ((0 : Site d) ∉ lma_corridorVerts j₁ L ∧ (0 : Site d) ∉ lma_corridorVerts j₂ L ∧
      (0 : Site d) ∉ lma_corridorVerts j₃ L) :=
  ⟨⟨lma_corridorVerts_disjoint hjd12 L, lma_corridorVerts_disjoint hjd13 L,
      lma_corridorVerts_disjoint hjd23 L⟩,
    lma_origin_notMem_corridorVerts j₁ L, lma_origin_notMem_corridorVerts j₂ L,
    lma_origin_notMem_corridorVerts j₃ L⟩


theorem lmg_attachData (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : crr_AxisAssignment ω x₁ j₁) (h2 : crr_AxisAssignment ω x₂ j₂)
    (h3 : crr_AxisAssignment ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ :=
  lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23
    (crr_clusterReachesRay_of_assignment ω x₁ j₁ h1)
    (crr_clusterReachesRay_of_assignment ω x₂ j₂ h2)
    (crr_clusterReachesRay_of_assignment ω x₃ j₃ h3)


theorem lmg_attachData_of_candidates (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (S : Fin 3 → Finset (Fin d))
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
    tex_AttachData ω x₁ x₂ x₃ :=
  caa_attachData ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 h


theorem lmg_attachData_disjoint (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : crr_AxisAssignment ω x₁ j₁) (h2 : crr_AxisAssignment ω x₂ j₂)
    (h3 : crr_AxisAssignment ω x₃ j₃) :
    tex_AttachData ω x₁ x₂ x₃ ∧
      ∀ L : ℕ,
        (Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) ∧
          Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₃ L) ∧
          Disjoint (lma_corridorVerts j₂ L) (lma_corridorVerts j₃ L)) ∧
        ((0 : Site d) ∉ lma_corridorVerts j₁ L ∧ (0 : Site d) ∉ lma_corridorVerts j₂ L ∧
          (0 : Site d) ∉ lma_corridorVerts j₃ L) :=
  ⟨lmg_attachData ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3,
    fun L => lmg_corridors_disjoint hjd12 hjd13 hjd23 L⟩


theorem lmg_threeClustersReachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : crr_AxisAssignment ω x₁ j₁) (h2 : crr_AxisAssignment ω x₂ j₂)
    (h3 : crr_AxisAssignment ω x₃ j₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ ⟨hcd12, hcd13, hcd23⟩
    (lmg_attachData ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h1 h2 h3)


end Percolation
end StatMech
