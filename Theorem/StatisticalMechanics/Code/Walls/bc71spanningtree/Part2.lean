/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc70globalforest.Part4
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc71spanningtree
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


theorem bc71_globalForest_of_forestNeighbours (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc71_GnForestNeighbours ω L R) : bc69_Gn_globalForest ω L R := by
  classical
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, hacyc, hmin, hnbr, hιinj, hleaf⟩ := h
  refine ⟨S, hSfin, hSne, G, hGdec, ιU, hacyc, hmin, ?_, hιinj, hleaf⟩
  
  intro y hybox htri
  obtain ⟨v₁, v₂, v₃, hadj₁, hadj₂, hadj₃, hcut₁₂, hcut₁₃, hcut₂₃⟩ := hnbr y hybox htri
  exact bc71_deg3_of_cutArms_subtype ω L y G hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃


theorem bc71_count_of_forestNeighbours (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc71_GnForestNeighbours ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_coarseTcount_le_boundary ω L R (bc71_globalForest_of_forestNeighbours ω L R h)


theorem bc71_infiniteClusters_top_null_of_forestNeighbours
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hNbr : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc71_GnForestNeighbours ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc69_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L
    (fun ω R => bc71_globalForest_of_forestNeighbours ω L R (hNbr ω R)) hcoarseRoute


open Classical in


theorem bc71_Gn_spanForest_degree (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) (L : ℕ)
    {y : Site d} (hy : y ∈ box d R)
    {v₁ v₂ v₃ : (↑(box d R) : Type)}
    (hadj₁ : (bc70_spanningForest ω R).Adj ⟨y, hy⟩ v₁)
    (hadj₂ : (bc70_spanningForest ω R).Adj ⟨y, hy⟩ v₂)
    (hadj₃ : (bc70_spanningForest ω R).Adj ⟨y, hy⟩ v₃)
    (hcut₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₂ : Site d))
    (hcut₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₃ : Site d))
    (hcut₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₂ : Site d) (v₃ : Site d)) :
    3 ≤ (bc70_spanningForest ω R).degree ⟨y, hy⟩ := by
  classical
  
  exact bc71_deg3_of_cutArms_subtype (S := box d R) ω L y (bc70_spanningForest ω R)
    hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃


theorem bc71_upperLines_deg3 {L R : ℕ} (hL : 3 ≤ L) (hR3 : 4 ≤ R)
    (hsingle : ∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation bc60_upperLines L y → y = 0) :
    bc69_Gn_globalForest bc60_upperLines L R :=
  bc70_upperLines_globalForest hL hR3 hsingle


theorem bc71_star_centre_deg3 : bc70_star4.degree 0 = 3 := bc70_star4_deg0


theorem bc71_degree_collapse_possible :
    ∃ (D : ℕ) (ω : ConfigSpace (Sym2 (Site D))) (L : ℕ) (y a b : Site D),
      
      b ∈ bc61_boxAround D L y ∧ (openSubgraph D ω).Adj b a ∧ bc67_GnIncident ω L y a ∧
      
      
      ¬ (hypercubicLattice D).Adj y a := by
  classical
  
  
  set y : Site 1 := (fun _ => 0) with hy
  set b : Site 1 := (fun _ => 1) with hb
  set a : Site 1 := (fun _ => 2) with ha
  
  set ω : ConfigSpace (Sym2 (Site 1)) := fun e => decide (e = s(b, a)) with hω
  have hopen : ω s(b, a) = true := by rw [hω]; simp
  have hadjba : (hypercubicLattice 1).Adj b a := by
    rw [hypercubicLattice_adj, Fin.sum_univ_one]; rw [hb, ha]; decide
  refine ⟨1, ω, 1, y, a, b, ?_, ?_, ?_, ?_⟩
  · 
    rw [bc61_mem_boxAround, mem_box]
    intro i; rw [hb, hy]; simp
  · 
    rw [openSubgraph_adj]; exact ⟨hadjba, hopen⟩
  · 
    refine ⟨b, ?_, ?_⟩
    · rw [bc61_mem_boxAround, mem_box]; intro i; rw [hb, hy]; simp
    · rw [openSubgraph_adj]; exact ⟨hadjba, hopen⟩
  · 
    rw [hypercubicLattice_adj, Fin.sum_univ_one]; rw [hy, ha]; decide


theorem bc71_status :
    
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj] (u a₁ a₂ a₃ : V),
      G.Adj u a₁ → G.Adj u a₂ → G.Adj u a₃ → a₁ ≠ a₂ → a₁ ≠ a₃ → a₂ ≠ a₃ →
      3 ≤ G.degree u) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a₁ a₂ a₃ : Site d),
      ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ →
      ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ →
      ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃ →
      a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc71_GnForestNeighbours ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ G _ u a₁ a₂ a₃ h₁ h₂ h₃ h12 h13 h23
    exact bc71_deg3_of_three_neighbours G h₁ h₂ h₃ h12 h13 h23
  · intro ω L y a₁ a₂ a₃ hcut₁₂ hcut₁₃ hcut₂₃
    exact bc71_cutArms_distinct ω L hcut₁₂ hcut₁₃ hcut₂₃
  · intro ω L R h
    exact bc71_count_of_forestNeighbours ω L R h

end StatMech.Walls
