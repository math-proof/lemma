/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkfforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgfglobalforest.Part2
import Def.StatisticalMechanics.Code.Walls.bkfforest
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bkf_harm_of_cutTransfer_and_targets
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (G : SimpleGraph (↑S : Type)) (ιU : Site d → (↑S : Type))
    (htrans : bkf_CutTransfer ω L R G ιU)
    (htargets : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d)) :
    ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃ := by
  intro y hybox htri
  obtain ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, hn₁, hn₂, hn₃, hg₁, hg₂, hg₃, hb₁₂, hb₁₃, hb₂₃⟩ :=
    htargets y hybox htri
  exact ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, hn₁, hn₂, hn₃, hg₁, hg₂, hg₃,
    htrans y hybox htri t₁ t₂ hb₁₂, htrans y hybox htri t₁ t₃ hb₁₃, htrans y hybox htri t₂ t₃ hb₂₃⟩


theorem bkf_connectedForest_closes_of_cutTransfer
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    (htrans : bkf_CutTransfer ω L R G ιU)
    (htargets : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧
        ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d))
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R :=
  bkf_connectedForest_closes ω L R G hGac ιU
    (bkf_harm_of_cutTransfer_and_targets ω L R G ιU htrans htargets) hinj hFmin


theorem bkf_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_count_via_leafBound ω L R (bc110_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno)


theorem bkf_cutTransfer_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (G : SimpleGraph (↑S : Type)) (ιU : Site d → (↑S : Type))
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bkf_CutTransfer ω L R G ιU := by
  intro y hybox htri; exact absurd htri (hno y hybox)


theorem bkf_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
      {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
      (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj], G.IsAcyclic →
      ∀ (ιU : Site d → (↑S : Type)),
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
        ∃ t₁ t₂ t₃ : (↑S : Type),
          bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
          ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
          G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
          ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
          ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
          ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃) →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
        bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) →
      (∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
        (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
        (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
          G.Reachable a b → F.Reachable a b) →
        ∀ v : (↑S : Type), 1 ≤ F.degree v) →
      bc69_Gn_globalForest ω L R) ∧
    
    (¬ ((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 1 2) ∧
    
    (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
      {S : Set (Site d)} [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
      (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj], G.IsAcyclic →
      ∀ (ιU : Site d → (↑S : Type)), bkf_CutTransfer ω L R G ιU →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
        ∃ t₁ t₂ t₃ : (↑S : Type),
          bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
          ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
          G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
          ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₂ : Site d) ∧
          ¬ (bc67_contractedLattice ω L y).Reachable (t₁ : Site d) (t₃ : Site d) ∧
          ¬ (bc67_contractedLattice ω L y).Reachable (t₂ : Site d) (t₃ : Site d)) →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
        bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) →
      (∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
        (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
        (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
          G.Reachable a b → F.Reachable a b) →
        ∀ v : (↑S : Type), 1 ≤ F.degree v) →
      bc69_Gn_globalForest ω L R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R S _ _ G _ hGac ιU harm hinj hFmin
    exact bkf_connectedForest_closes ω L R G hGac ιU harm hinj hFmin
  · exact bkf_sharedLeaf_cut_survives
  · intro V _ _ G _ hac hmin; exact bkf_sharedLeaf_absorbed_in_count G hac hmin
  · intro ω L R S _ _ G _ hGac ιU htrans htargets hinj hFmin
    exact bkf_connectedForest_closes_of_cutTransfer ω L R G hGac ιU htrans htargets hinj hFmin

end StatMech.Walls
