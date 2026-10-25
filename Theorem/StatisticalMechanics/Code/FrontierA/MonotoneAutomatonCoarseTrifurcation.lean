/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbability.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkmmerge
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls


theorem removeBox_siteForce_eq (n : ℕ) (eta : ConfigSpace (Site 2)) :
    removeSites (bc61_boxAround 2 n 0)
        (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) =
      removeSites (bc61_boxAround 2 n 0) (siteToBond eta) := by
  classical
  rw [bc61_boxAround_zero]
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      unfold removeSites
      by_cases hinc : ∃ t ∈ boxFinsetBK 2 n, t ∈ s(x, y)
      · rw [if_pos hinc, if_pos hinc]
      · rw [if_neg hinc, if_neg hinc]
        have hx : x ∉ boxFinsetBK 2 n := by
          intro hx
          exact hinc ⟨x, hx, by simp⟩
        have hy : y ∉ boxFinsetBK 2 n := by
          intro hy
          exact hinc ⟨y, hy, by simp⟩
        simp [siteToBond_mk, forceSitesOccupied_apply, hx, hy]


theorem siteToBond_le_siteForce (n : ℕ) (eta : ConfigSpace (Site 2)) :
    siteToBond eta ≤
      siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta) := by
  apply siteToBond_mono
  intro x
  by_cases hx : x ∈ boxFinsetBK 2 n <;>
    simp [forceSitesOccupied_apply, hx]


theorem siteForce_box_allOpen (n : ℕ) (eta : ConfigSpace (Site 2)) :
    bff_BoxAllOpen
      (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      obtain ⟨hx, hy, _hadj⟩ := mem_boxEdges_iff.mp he
      simp [siteToBond_mk, forceSitesOccupied_apply,
        mem_boxFinsetBK_iff.mpr hx, mem_boxFinsetBK_iff.mpr hy]


theorem coarseTrif_siteForce_of_coarse (n : ℕ)
    (eta : ConfigSpace (Site 2))
    (h : bc61_IsCoarseTrifurcation (siteToBond eta) n 0) :
    bc61_IsCoarseTrifurcation
      (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n 0 := by
  obtain ⟨a₁, a₂, a₃, hi₁, hi₂, hi₃, hinf, hcut⟩ := h
  have hmono := siteToBond_le_siteForce n eta
  refine ⟨a₁, a₂, a₃, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hba⟩ := hi₁
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₂
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₃
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · simpa only [removeBox_siteForce_eq] using hinf
  · simpa only [removeBox_siteForce_eq] using hcut


theorem siteForce_faithfulAllOpenTrif_of_threeMeetBox
    (eta : ConfigSpace (Site 2)) (n : ℕ)
    (h : siteToBond eta ∈ threeMeetBox 2 n) :
    FaithfulAllOpenTrifAt
      (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n 0 := by
  obtain ⟨_htop, x₁, x₂, x₃, hb₁, hb₂, hb₃,
    hi₁, hi₂, hi₃, hd₁₂, hd₁₃, hd₂₃⟩ := h
  have hcoarse : bc61_IsCoarseTrifurcation (siteToBond eta) n 0 :=
    bkm_coarseTrif_of_le (le_refl n) hb₁ hb₂ hb₃
      hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃
  refine ⟨?_, bgf2_indexAllOpen_zero_of_bff (siteForce_box_allOpen n eta)⟩
  rw [bgf2_centre_zero]
  exact (bc67_coarseTrif_is_G_n_trifurcation _ n 0).mp
    (coarseTrif_siteForce_of_coarse n eta hcoarse)


end StatMech.FrontierA
