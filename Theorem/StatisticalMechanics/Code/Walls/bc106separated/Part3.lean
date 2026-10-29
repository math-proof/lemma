/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc105contraction
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Theorem.StatisticalMechanics.Code.Walls.bc73sublattice.Part5
import Def.StatisticalMechanics.Code.Walls.bc106separated.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


open Classical in


theorem bc106_separatedContractedTrifGraph_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
    bc106_SeparatedContractedTrifGraph ω L R := by
  classical
  set S : Set (Site d) := {z₀, z₁} with hS
  have hz₀S : z₀ ∈ S := by rw [hS]; left; rfl
  have hz₁S : z₁ ∈ S := by rw [hS]; right; rfl
  haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  set a : (↑S : Type) := ⟨z₀, hz₀S⟩ with ha
  set b : (↑S : Type) := ⟨z₁, hz₁S⟩ with hb
  have hab : a ≠ b := by intro h; exact hzne (congrArg Subtype.val h)
  let G : SimpleGraph (↑S : Type) := SimpleGraph.fromEdgeSet {s(a, b)}
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  have hGac : G.IsAcyclic := bc69_single_edge_acyclic a b hab
  haveI hFdec : DecidableRel (osf_spanForest G).Adj := Classical.decRel _
  have hVall : ∀ v : (↑S : Type), v = a ∨ v = b := by
    intro v; obtain ⟨x, hx⟩ := v
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  have hFa : (osf_spanForest G).degree a = 1 := by
    rw [osf_spanForest_degree_of_acyclic G hGac a]; exact bc69_single_edge_degree a b hab
  have hFb : (osf_spanForest G).degree b = 1 := by
    rw [osf_spanForest_degree_of_acyclic G hGac b]; exact bc69_single_edge_degree_b a b hab
  refine ⟨S, hSfin, ⟨a⟩, G, hGdec, hFdec, (fun _ => a), ?_, ?_, ?_, ?_⟩
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro v; rcases hVall v with rfl | rfl
    · rw [hFa]
    · rw [hFb]
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro v _; rcases hVall v with rfl | rfl
    · exact hz₀
    · exact hz₁


theorem bc106_separatedCount_of_contractedGraph (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc106_SeparatedContractedTrifGraph ω L R) :
    bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
  classical
  obtain ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hmin, hιinj, hleaf⟩ := h
  
  have hdeg3 : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y →
      3 ≤ (osf_spanForest G).degree (ιU y) := by
    intro y hybox htri
    obtain ⟨v₁, v₂, v₃, ha₁, ha₂, ha₃, hc₁₂, hc₁₃, hc₂₃⟩ := hnbr y hybox htri
    exact bc103_deg3_spanForest_of_noBypass G ha₁ ha₂ ha₃ hc₁₂ hc₁₃ hc₂₃
  set Tf := bc106_separatedTrifFinset ω L R with hTf
  set Tw : Finset (↑S : Type) := Tf.image ιU with hTw
  
  have hmemTf : ∀ {y : Site d}, y ∈ Tf ↔ y ∈ box d R ∧ bc106_SeparatedCoarseTrif ω L y := by
    intro y
    rw [hTf, bc106_separatedTrifFinset, Finset.mem_filter, bc61_mem_coarseTrifFinset,
      bc106_SeparatedCoarseTrif]
    tauto
  have hιinjOn : Set.InjOn ιU Tf := by
    intro y hy z hz hyz
    rw [Finset.mem_coe, hmemTf] at hy hz
    exact hιinj y hy.1 hy.2 z hz.1 hz.2 hyz
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ (osf_spanForest G).degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨y, hyT, rfl⟩ := hw
    rw [hmemTf] at hyT
    exact hdeg3 y hyT.1 hyT.2
  calc bc106_separatedTcount ω L R = Tf.card := rfl
    _ = Tw.card := hcardTw.symm
    _ ≤ (univ.filter (fun v => 3 ≤ (osf_spanForest G).degree v)).card :=
        flc2_trifImage_card_le_deg3 (osf_spanForest G) Tw hTwdeg
    _ ≤ (univ.filter (fun v => (osf_spanForest G).degree v = 1)).card :=
        flc2_forest_internal_le_leaves (osf_spanForest G) (osf_spanForest_acyclic G) hmin
    _ ≤ boxSV_boundaryCard d R :=
        flc2_leaf_card_le_boundary (osf_spanForest G) R (fun v => (v : Site d)) hleaf
          (by
            
            intro v hv w hw hvw
            exact Subtype.ext hvw)


theorem bc106_separatedContractedTrifGraph_of_bc103 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) : bc106_SeparatedContractedTrifGraph ω L R := by
  obtain ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hmin, hιinj, hleaf⟩ := h
  refine ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, ?_, hmin, ?_, hleaf⟩
  · intro y hybox hsep
    exact hnbr y hybox (bc106_gnTrif_of_separated hsep)
  · intro y hybox hsep z hzbox hsepz hUeq
    exact hιinj y hybox (bc106_gnTrif_of_separated hsep) z hzbox
      (bc106_gnTrif_of_separated hsepz) hUeq


theorem bc106_origin_event_eq (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) :
    bc106_SeparatedCoarseTrif ω L (0 : Site d) ↔ bc61_IsCoarseTrifurcation ω L (0 : Site d) := by
  unfold bc106_SeparatedCoarseTrif
  exact ⟨fun h => h.1, fun h => ⟨h, bc106_origin_onSublattice L⟩⟩


theorem bc106_full_covering_of_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc73_SublatticeForest ω L R) :
    bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R :=
  bc73_covering ω L R h


theorem bc106_separated_drives_prob_zero
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R) :
    μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 :=
  bc73_coarseTrif_prob_eq_zero_of_sublatticeForest μ hd L hexp hforest


theorem bc106_separated_drives_dichotomy
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc73_infiniteClusters_top_null μ hd L hexp hforest hexist


theorem bc106_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y z : Site d),
      bc106_SeparatedCoarseTrif ω L y → bc106_SeparatedCoarseTrif ω L z → y ≠ z →
      Disjoint (bc61_boxAround d L y) (bc61_boxAround d L z)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc103_ContractedTrifGraph ω L R → bc106_SeparatedContractedTrifGraph ω L R) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc106_SeparatedContractedTrifGraph ω L R →
      bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc73_SublatticeForest ω L R → bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ),
      bc106_SeparatedCoarseTrif ω L (0 : Site d) ↔ bc61_IsCoarseTrifurcation ω L (0 : Site d)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ω L y z hy hz hne; exact bc106_boxes_disjoint hy hz hne
  · intro ω L R h; exact bc106_separatedContractedTrifGraph_of_bc103 ω L R h
  · intro ω L R h; exact bc106_separatedCount_of_contractedGraph ω L R h
  · intro ω L R h; exact bc106_separated_count_le_boundary_of_forest ω L R h
  · intro ω L; exact bc106_origin_event_eq ω L

end StatMech.Walls
