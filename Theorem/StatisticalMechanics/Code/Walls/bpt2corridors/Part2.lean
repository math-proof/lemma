/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bxpxpos.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Walls.bpt2corridors.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bpt2_removeSite_closeI_congr (I : Finset (Sym2 (Site 2)))
    {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (hag : agreeOn ((↑I : Set (Sym2 (Site 2)))ᶜ) ω ω') :
    removeSite 0 (bpt2_closeI I ω) = removeSite 0 (bpt2_closeI I ω') := by
  funext e
  by_cases h0 : (0 : Site 2) ∈ e
  · simp [removeSite, h0]
  · simp only [removeSite, h0, if_false]
    unfold bpt2_closeI
    by_cases hI : e ∈ I
    · simp [hI]
    · simp only [hI, if_false]
      exact (hag e (by simp only [Set.mem_compl_iff, Finset.mem_coe]; exact hI)).symm


theorem bpt2_Ext_dependsOn (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) :
    DependsOn (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) ((↑I : Set (Sym2 (Site 2)))ᶜ) := by
  intro ω ω' hag
  change bpt2_ExtPred I a₁ a₂ a₃ x₁ x₂ x₃ (removeSite 0 (bpt2_closeI I ω))
      ↔ bpt2_ExtPred I a₁ a₂ a₃ x₁ x₂ x₃ (removeSite 0 (bpt2_closeI I ω'))
  rw [bpt2_removeSite_closeI_congr I hag]


theorem bpt2_hgeo (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2)
    (η₀ : ConfigSpace ↥I)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
      Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃) :
    cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃
      ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
  rintro ω ⟨hcyl, S₁, S₂, S₃, ⟨ha1, ha2, ha3⟩, ⟨hx1, hx2, hx3⟩, ⟨hd12, hd13, hd23⟩,
    ⟨hIr1, hIr2, hIr3⟩, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩⟩
  obtain ⟨conn1, conn2, conn3⟩ := hcorr ω hcyl
  have hsub1 : cluster 2 (removeSite 0 ω) a₁ ⊆ S₁ := bpt2_cluster_confined I ω ha1 hIr1 hc1
  have hsub2 : cluster 2 (removeSite 0 ω) a₂ ⊆ S₂ := bpt2_cluster_confined I ω ha2 hIr2 hc2
  have hsub3 : cluster 2 (removeSite 0 ω) a₃ ⊆ S₃ := bpt2_cluster_confined I ω ha3 hIr3 hc3
  have hle : removeSite 0 (bpt2_closeI I ω) ≤ removeSite 0 ω :=
    bpt2_removeSite_mono (bpt2_closeI_le I ω) 0
  refine ⟨hne, hadj, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [cluster_eq_of_connected conn1]; exact hi1.mono (cluster_mono hle x₁)
    · rw [cluster_eq_of_connected conn2]; exact hi2.mono (cluster_mono hle x₂)
    · rw [cluster_eq_of_connected conn3]; exact hi3.mono (cluster_mono hle x₃)
  · refine ⟨?_, ?_, ?_⟩
    · intro hconn; exact (Set.disjoint_left.mp hd12) (hsub1 (mem_cluster.mpr hconn)) ha2
    · intro hconn; exact (Set.disjoint_left.mp hd13) (hsub1 (mem_cluster.mpr hconn)) ha3
    · intro hconn; exact (Set.disjoint_left.mp hd23) (hsub2 (mem_cluster.mpr hconn)) ha3


theorem bpt2_precursorPos_of_residues
    (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
      Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃)
    (hindep : bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)
        = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (cylinder I ({η₀} : Set (ConfigSpace ↥I)))
          * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
              (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃))
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (NeighborTrifPrecursor 2 a₁ a₂ a₃) :=
  bdec_precursorPos_of_decoupled p hp1 hp0 hplt a₁ a₂ a₃ I η₀
    (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) hindep hXpos
    (bpt2_hgeo I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr)


end StatMech.Walls
