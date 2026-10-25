/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Def.StatisticalMechanics.Code.Percolation.TrifurcationFiniteEnergy.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfe_reachOrigin_of_contact (ω : ConfigSpace (Sym2 (Site d)))
    (h : tfe_TrifurcationContact ω) : mco_ThreeClustersReachOrigin ω := by
  obtain ⟨a₁, a₂, a₃, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  exact ⟨a₁, a₂, a₃, a₁, a₂, a₃, hadj,
    ⟨connected_rfl, connected_rfl, connected_rfl⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩


theorem tfe_contact_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) : tfe_TrifurcationContact ω := by
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  have e1 : cluster d (removeSite 0 ω) a₁ = cluster d (removeSite 0 ω) x₁ :=
    cluster_eq_of_connected hc1
  have e2 : cluster d (removeSite 0 ω) a₂ = cluster d (removeSite 0 ω) x₂ :=
    cluster_eq_of_connected hc2
  have e3 : cluster d (removeSite 0 ω) a₃ = cluster d (removeSite 0 ω) x₃ :=
    cluster_eq_of_connected hc3
  refine ⟨a₁, a₂, a₃, hadj, ⟨e1 ▸ hi1, e2 ▸ hi2, e3 ▸ hi3⟩, ?_, ?_, ?_⟩
  · rw [e1, e2]; exact hd12
  · rw [e1, e3]; exact hd13
  · rw [e2, e3]; exact hd23


theorem tfe_reachOrigin_iff_contact (ω : ConfigSpace (Sym2 (Site d))) :
    mco_ThreeClustersReachOrigin ω ↔ tfe_TrifurcationContact ω :=
  ⟨tfe_contact_of_reachOrigin ω, tfe_reachOrigin_of_contact ω⟩


theorem tfe_contact_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    tfe_TrifurcationContact ω :=
  ⟨a₁, a₂, a₃, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩


theorem tfe_reachOrigin_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
    (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
    (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    mco_ThreeClustersReachOrigin ω :=
  tfe_reachOrigin_of_contact ω
    (tfe_contact_of_neighbour_witnesses ω a₁ a₂ a₃ hadj hi1 hi2 hi3 hd12 hd13 hd23)


theorem tfe_attach_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧
      (hypercubicLattice d).Adj 0 x₃)
    (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
    tex_AttachData ω x₁ x₂ x₃ :=
  tex_attachData_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri

end Percolation
end StatMech
