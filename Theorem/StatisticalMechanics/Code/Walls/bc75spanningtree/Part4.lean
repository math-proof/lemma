/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc74disjointforest.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Def.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
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


theorem bc75_fiberForest_of_gnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    bc74_FiberForest ω L R c := by
  classical
  obtain ⟨S, hSfin, hSne, hyS, htriData, hmin, hleaf⟩ := h
  
  set w₀ : (↑S : Type) := hSne.some with hw₀
  set ιU : Site d → (↑S : Type) :=
    fun y => if hy : y ∈ bc73_fiber ω L R c then ⟨y, hyS y hy⟩ else w₀ with hιU
  have hιUeq : ∀ y (hy : y ∈ bc73_fiber ω L R c), ιU y = ⟨y, hyS y hy⟩ := by
    intro y hy; simp only [hιU, dif_pos hy]
  refine ⟨S, hSfin, hSne, bc75_spanForest ω L R c S, Classical.decRel _, ιU,
    bc75_spanForest_acyclic ω L R c S, hmin, ?_, ?_, hleaf⟩
  · 
    intro y hy
    rw [hιUeq y hy]
    obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, hc₁₂, hc₁₃, hc₂₃⟩ := htriData y hy
    exact bc75_deg3_in_spanForest_of_gnCut ω L R c (hyS y hy) h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · 
    intro y hy z hz hyz
    rw [hιUeq y hy, hιUeq z hz] at hyz
    exact congrArg Subtype.val hyz


theorem bc75_fiber_count_of_gnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (h : bc75_FiberGnTrifData ω L R c) :
    (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R :=
  bc74_fiber_count_of_fiberForest ω L R c (bc75_fiberForest_of_gnTrifData ω L R c h)


theorem bc75_sublatticeForest_of_gnTrifData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
    bc73_SublatticeForest ω L R :=
  fun c => bc75_fiber_count_of_gnTrifData ω L R c (h c)


theorem bc75_emptyFiber_collapse_id (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅) (x : Site d) :
    bc75_collapseFiber ω L R c x = x := by
  apply bc75_collapseFiber_id
  intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)


theorem bc75_emptyFiber_box_adj (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅)
    {z₀ z₁ : Site d} (hopen : (openSubgraph d ω).Adj z₀ z₁)
    (hz₀ : z₀ ∈ ({z₀, z₁} : Set (Site d))) (hz₁ : z₁ ∈ ({z₀, z₁} : Set (Site d))) :
    (bc75_fiberQuotBox ω L R c ({z₀, z₁} : Set (Site d))).Adj ⟨z₀, hz₀⟩ ⟨z₁, hz₁⟩ := by
  have hne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  
  change (bc75_fiberQuot ω L R c).Adj z₀ z₁
  exact ⟨hne, z₀, z₁, bc75_emptyFiber_collapse_id ω L R c hempty z₀,
    bc75_emptyFiber_collapse_id ω L R c hempty z₁, hopen⟩

open Classical in


theorem bc75_fiberGnTrifData_of_emptyFiber (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (c : Fin d → Fin (2 * L + 1)) (hempty : bc73_fiber ω L R c = ∅)
    {z₀ z₁ : Site d} (hz₀b : z₀ ∈ vertexBoundary d R) (hz₁b : z₁ ∈ vertexBoundary d R)
    (hopen : (openSubgraph d ω).Adj z₀ z₁) :
    bc75_FiberGnTrifData ω L R c := by
  classical
  set S : Set (Site d) := {z₀, z₁} with hSdef
  have hz₀S : z₀ ∈ S := by rw [hSdef]; left; rfl
  have hz₁S : z₁ ∈ S := by rw [hSdef]; right; rfl
  have hne : z₀ ≠ z₁ := (openSubgraph d ω).ne_of_adj hopen
  haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  
  have hVall : ∀ v : (↑S : Type), v = ⟨z₀, hz₀S⟩ ∨ v = ⟨z₁, hz₁S⟩ := by
    intro v; obtain ⟨x, hx⟩ := v
    rw [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  
  have hcard2 : ENat.card (↑S : Type) ≤ 2 := by
    rw [ENat.card_eq_coe_natCard]
    have : Nat.card (↑S : Type) ≤ 2 := by
      have hle : (S : Set (Site d)).ncard ≤ 2 := by
        rw [hSdef]; exact (Set.ncard_insert_le _ _).trans (by simp [Set.ncard_singleton])
      simpa [Nat.card_coe_set_eq] using hle
    exact_mod_cast this
  have hGac : (bc75_fiberQuotBox ω L R c S).IsAcyclic := SimpleGraph.IsAcyclic.of_card_le_two hcard2
  
  have hSF : bc75_spanForest ω L R c S = bc75_fiberQuotBox ω L R c S :=
    osf_spanForest_of_acyclic (bc75_fiberQuotBox ω L R c S) hGac
  
  have hedge : (bc75_fiberQuotBox ω L R c S).Adj ⟨z₀, hz₀S⟩ ⟨z₁, hz₁S⟩ :=
    bc75_emptyFiber_box_adj ω L R c hempty hopen hz₀S hz₁S
  haveI hGdec : DecidableRel (bc75_fiberQuotBox ω L R c S).Adj := Classical.decRel _
  have hne' : (⟨z₀, hz₀S⟩ : (↑S : Type)) ≠ ⟨z₁, hz₁S⟩ := fun h => hne (Subtype.ext_iff.mp h)
  
  have hns₀ : (bc75_fiberQuotBox ω L R c S).neighborSet ⟨z₀, hz₀S⟩ = {⟨z₁, hz₁S⟩} := by
    ext w; rw [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    rcases hVall w with rfl | rfl
    · exact ⟨fun h => absurd rfl ((bc75_fiberQuotBox ω L R c S).ne_of_adj h), fun h =>
        absurd h fun hh => hne' (by rw [hh])⟩
    · exact ⟨fun _ => rfl, fun _ => hedge⟩
  have hns₁ : (bc75_fiberQuotBox ω L R c S).neighborSet ⟨z₁, hz₁S⟩ = {⟨z₀, hz₀S⟩} := by
    ext w; rw [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    rcases hVall w with rfl | rfl
    · exact ⟨fun _ => rfl, fun _ => hedge.symm⟩
    · exact ⟨fun h => absurd rfl ((bc75_fiberQuotBox ω L R c S).ne_of_adj h), fun h =>
        absurd h fun hh => hne' (by rw [hh])⟩
  
  have hdeg : ∀ v : (↑S : Type), (bc75_spanForest ω L R c S).degree v = 1 := by
    intro v
    rw [hSF, SimpleGraph.degree, SimpleGraph.neighborFinset_def]
    rcases hVall v with rfl | rfl
    · simp only [hns₀, Set.toFinset_singleton, Finset.card_singleton]
    · simp only [hns₁, Set.toFinset_singleton, Finset.card_singleton]
  refine ⟨S, hSfin, ⟨⟨z₀, hz₀S⟩⟩, ?_, ?_, ?_, ?_⟩
  · 
    intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)
  · 
    intro y hy; rw [hempty] at hy; exact absurd hy (Finset.notMem_empty y)
  · 
    intro v; rw [hdeg v]
  · 
    intro v _
    rcases hVall v with rfl | rfl
    · exact hz₀b
    · exact hz₁b


theorem bc75_sublatticeForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀b : z₀ ∈ vertexBoundary d R) (hz₁b : z₁ ∈ vertexBoundary d R)
    (hopen : (openSubgraph d ω).Adj z₀ z₁) (hno : bc61_coarseTrifFinset ω L R = ∅) :
    bc73_SublatticeForest ω L R := by
  classical
  refine bc75_sublatticeForest_of_gnTrifData ω L R (fun c => ?_)
  have hfib : bc73_fiber ω L R c = ∅ := by rw [bc73_fiber, hno]; simp
  exact bc75_fiberGnTrifData_of_emptyFiber ω L R c hfib hz₀b hz₁b hopen


theorem bc75_bk_count_closed_of_gnTrifData
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d) (L : ℕ)
    (hexp : ∀ R : ℕ,
      ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
        = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
    (hData : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c)
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc73_infiniteClusters_top_null μ hd L hexp
    (fun ω R => bc75_sublatticeForest_of_gnTrifData ω L R (fun c => hData ω R c)) hexist


theorem bc75_upperLines_openBoundaryEdge {R : ℕ} (hR : 1 ≤ R) :
    (bc57_pt 0 (R : ℤ) ∈ vertexBoundary 2 R) ∧ (bc57_pt 1 (R : ℤ) ∈ vertexBoundary 2 R) ∧
      (openSubgraph 2 bc60_upperLines).Adj (bc57_pt 0 (R : ℤ)) (bc57_pt 1 (R : ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · 
    rw [vertexBoundary, Set.mem_diff]
    refine ⟨?_, ?_⟩
    · rw [mem_box]; intro i; fin_cases i
      · change ((bc57_pt 0 (R : ℤ)) 0).natAbs ≤ R; rw [bc57_pt_fst]; simp
      · change ((bc57_pt 0 (R : ℤ)) 1).natAbs ≤ R; rw [bc57_pt_snd]; simp
    · rw [mem_box]; simp only [not_forall, not_le]
      refine ⟨1, ?_⟩
      have : ((bc57_pt 0 (R : ℤ)) 1).natAbs = R := by rw [bc57_pt_snd]; exact Int.natAbs_natCast R
      rw [this]; omega
  · 
    rw [vertexBoundary, Set.mem_diff]
    refine ⟨?_, ?_⟩
    · rw [mem_box]; intro i; fin_cases i
      · change ((bc57_pt 1 (R : ℤ)) 0).natAbs ≤ R; rw [bc57_pt_fst]; simp; omega
      · change ((bc57_pt 1 (R : ℤ)) 1).natAbs ≤ R; rw [bc57_pt_snd]; simp
    · rw [mem_box]; simp only [not_forall, not_le]
      refine ⟨1, ?_⟩
      have : ((bc57_pt 1 (R : ℤ)) 1).natAbs = R := by rw [bc57_pt_snd]; exact Int.natAbs_natCast R
      rw [this]; omega
  · 
    rw [openSubgraph_adj]
    refine ⟨?_, ?_⟩
    · 
      rw [hypercubicLattice_adj]
      rw [Fin.sum_univ_two]
      simp only [bc57_pt_fst, bc57_pt_snd]
      norm_num
    · 
      have := bc60_open 0 (h := (R : ℤ)) (by exact_mod_cast hR)
      simpa using this


theorem bc75_upperLines_emptyFiber_gnTrifData {L R : ℕ} (hR : 1 ≤ R)
    (c : Fin 2 → Fin (2 * L + 1)) (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
    bc75_FiberGnTrifData bc60_upperLines L R c := by
  obtain ⟨hb0, hb1, hopen⟩ := bc75_upperLines_openBoundaryEdge hR
  exact bc75_fiberGnTrifData_of_emptyFiber bc60_upperLines L R c hempty hb0 hb1 hopen


theorem bc75_upperLines_gnCut_needs_buffer (L : ℕ) :
    Disjoint (bc61_boxAround 2 L (0 : Site 2))
        (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
      Connected 2 bc60_upperLines
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) :=
  bc74_upperLines_arms_can_share_boundary L


theorem bc75_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1))
      (S : Set (Site d)) (_ : Fintype (↑S : Type)), (bc75_spanForest ω L R c S).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)),
      bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      (∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) →
      bc73_SublatticeForest ω L R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R c S _; exact bc75_spanForest_acyclic ω L R c S
  · intro ω L R c h; exact bc75_fiber_count_of_gnTrifData ω L R c h
  · intro ω L R h; exact bc75_sublatticeForest_of_gnTrifData ω L R h

end StatMech.Walls
