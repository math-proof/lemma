/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc103contractdeg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc103contractdeg
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


theorem bc103_globalForest_of_contractedGraph (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) : bc69_Gn_globalForest ω L R := by
  classical
  obtain ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hmin, hιinj, hleaf⟩ := h
  refine ⟨S, hSfin, hSne, osf_spanForest G, hFdec, ιU, osf_spanForest_acyclic G, hmin, ?_,
    hιinj, hleaf⟩
  
  intro y hybox htri
  obtain ⟨v₁, v₂, v₃, hadj₁, hadj₂, hadj₃, hcut₁₂, hcut₁₃, hcut₂₃⟩ := hnbr y hybox htri
  exact bc103_deg3_spanForest_of_noBypass G hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃


theorem bc103_count_of_contractedGraph (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_coarseTcount_le_boundary ω L R (bc103_globalForest_of_contractedGraph ω L R h)


theorem bc103_infiniteClusters_top_null_of_contractedGraph
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hCon : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc103_ContractedTrifGraph ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc69_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L
    (fun ω R => bc103_globalForest_of_contractedGraph ω L R (hCon ω R)) hcoarseRoute


theorem bc103_status :
    
    (∀ {V : Type} [Fintype V] (G F : SimpleGraph V) [DecidableRel F.Adj],
      F ≤ G → (∀ a b, G.Reachable a b → F.Reachable a b) →
      ∀ (u v₁ v₂ v₃ : V), G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      3 ≤ F.degree u) ∧
    
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel (osf_spanForest G).Adj]
      (u v₁ v₂ v₃ : V), G.Adj u v₁ → G.Adj u v₂ → G.Adj u v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₂ →
      ¬ (G.deleteIncidenceSet u).Reachable v₁ v₃ →
      ¬ (G.deleteIncidenceSet u).Reachable v₂ v₃ →
      3 ≤ (osf_spanForest G).degree u) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc103_ContractedTrifGraph ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ G F _ hFG hFr u v₁ v₂ v₃ h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
    exact bc103_deg3_of_noBypass hFG hFr h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · intro V _ G _ u v₁ v₂ v₃ h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
    exact bc103_deg3_spanForest_of_noBypass G h₁ h₂ h₃ hc₁₂ hc₁₃ hc₂₃
  · intro ω L R h
    exact bc103_count_of_contractedGraph ω L R h

end StatMech.Walls
