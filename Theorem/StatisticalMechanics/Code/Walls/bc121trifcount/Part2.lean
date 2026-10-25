/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc112sepcontract.Part7
import Theorem.StatisticalMechanics.Code.Walls.bc118pathmember
import Def.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
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


open Classical in


theorem bc121_globalForest_of_peel2
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R := by
  classical
  
  set P : (↑S : Type) → Prop := bc121_Protected ω L R ιU with hP
  haveI : DecidablePred P := Classical.decPred _
  obtain ⟨F, hFdec, hFle, hFac, hFleafP, hFpres⟩ :=
    bc121_boundaryAnchored_subforest G P hGac
  
  have hFmin' : ∀ v : (↑S : Type), 1 ≤ F.degree v := hFmin F hFle hFac hFleafP hFpres
  
  have hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ F.degree (ιU y) := by
    intro y hybox htri
    obtain ⟨t₁, t₂, t₃, hp₁, hp₂, hp₃, hne₁, hne₂, hne₃, hgr₁, hgr₂, hgr₃,
      hgc₁₂, hgc₁₃, hgc₂₃⟩ := harm y hybox htri
    
    have hhubP : P (ιU y) := Or.inr ⟨y, hybox, htri, rfl⟩
    
    have hfr₁ : F.Reachable (ιU y) t₁ := hFpres _ _ hhubP hp₁ hgr₁
    have hfr₂ : F.Reachable (ιU y) t₂ := hFpres _ _ hhubP hp₂ hgr₂
    have hfr₃ : F.Reachable (ιU y) t₃ := hFpres _ _ hhubP hp₃ hgr₃
    
    have hdile : F.deleteIncidenceSet (ιU y) ≤ G.deleteIncidenceSet (ιU y) := by
      intro a b hab
      rw [SimpleGraph.deleteIncidenceSet_adj] at hab ⊢
      exact ⟨hFle hab.1, hab.2.1, hab.2.2⟩
    have hcutmono : ∀ t t' : (↑S : Type),
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t t' →
        ¬ (F.deleteIncidenceSet (ιU y)).Reachable t t' := by
      intro t t' hg hf
      exact hg (hf.mono hdile)
    exact bc121_deg3_of_three_reached_targets F hne₁ hne₂ hne₃ hfr₁ hfr₂ hfr₃
      (hcutmono t₁ t₂ hgc₁₂) (hcutmono t₁ t₃ hgc₁₃) (hcutmono t₂ t₃ hgc₂₃)
  
  
  have hFleaf : ∀ v : (↑S : Type), F.degree v = 1 → (v : Site d) ∈ vertexBoundary d R := by
    intro v hv
    rcases hFleafP v hv with hb | ⟨y, hybox, htri, hyv⟩
    · exact hb
    · 
      exfalso
      have : 3 ≤ F.degree v := hyv ▸ hdeg3 y hybox htri
      omega
  exact ⟨S, hSfin, hSne, F, hFdec, ιU, hFac, hFmin', hdeg3, hinj, hFleaf⟩


theorem bc121_count_via_peel2
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} [hSfin : Fintype (↑S : Type)] [hSne : Nonempty (↑S : Type)]
    (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj] (hGac : G.IsAcyclic)
    (ιU : Site d → (↑S : Type))
    (harm : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y →
      ∃ t₁ t₂ t₃ : (↑S : Type),
        bc121_Protected ω L R ιU t₁ ∧ bc121_Protected ω L R ιU t₂ ∧ bc121_Protected ω L R ιU t₃ ∧
        ιU y ≠ t₁ ∧ ιU y ≠ t₂ ∧ ιU y ≠ t₃ ∧
        G.Reachable (ιU y) t₁ ∧ G.Reachable (ιU y) t₂ ∧ G.Reachable (ιU y) t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₁ t₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable t₂ t₃)
    (hinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hFmin : ∀ (F : SimpleGraph (↑S : Type)) [DecidableRel F.Adj], F ≤ G → F.IsAcyclic →
      (∀ v : (↑S : Type), F.degree v = 1 → bc121_Protected ω L R ιU v) →
      (∀ a b : (↑S : Type), bc121_Protected ω L R ιU a → bc121_Protected ω L R ιU b →
        G.Reachable a b → F.Reachable a b) →
      ∀ v : (↑S : Type), 1 ≤ F.degree v) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R
    (bc121_globalForest_of_peel2 ω L R G hGac ιU harm hinj hFmin)


theorem bc121_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc118_count_closes_via_forest ω L R (bc110_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno)


theorem bc121_status :
    
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (B : V → Prop) [DecidablePred B], G.IsAcyclic →
      ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj),
        F ≤ G ∧ F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v) ∧
        (∀ a b, B a → B b → G.Reachable a b → F.Reachable a b)) ∧
    
    (∀ {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj] (u t₁ t₂ t₃ : V),
      u ≠ t₁ → u ≠ t₂ → u ≠ t₃ →
      F.Reachable u t₁ → F.Reachable u t₂ → F.Reachable u t₃ →
      ¬ (F.deleteIncidenceSet u).Reachable t₁ t₂ →
      ¬ (F.deleteIncidenceSet u).Reachable t₁ t₃ →
      ¬ (F.deleteIncidenceSet u).Reachable t₂ t₃ →
      3 ≤ F.degree u) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ G _ B _ hac; exact bc121_boundaryAnchored_subforest G B hac
  · intro V _ F _ u t₁ t₂ t₃ h₁ h₂ h₃ r₁ r₂ r₃ c₁₂ c₁₃ c₂₃
    exact bc121_deg3_of_three_reached_targets F h₁ h₂ h₃ r₁ r₂ r₃ c₁₂ c₁₃ c₂₃
  · intro ω L R h; exact bc118_count_closes_via_forest ω L R h

end StatMech.Walls
