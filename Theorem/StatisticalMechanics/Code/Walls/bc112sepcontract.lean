/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc110globalforest
import Theorem.StatisticalMechanics.Code.Walls.bc106separated.Part3
import Def.StatisticalMechanics.Code.Walls.bc112sepcontract
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


theorem bc112_separatedArmGraph_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ : Site d}
    (hno : ∀ y, y ∈ box d R → ¬ bc106_SeparatedCoarseTrif ω L y) :
    bc112_SeparatedArmGraph ω L R := by
  classical
  set S : Set (Site d) := {z₀} with hS
  have hz₀S : z₀ ∈ S := by rw [hS]; rfl
  haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  set a : (↑S : Type) := ⟨z₀, hz₀S⟩ with ha
  let G : SimpleGraph (↑S : Type) := ⊥
  haveI hGdec : DecidableRel G.Adj := fun _ _ => instDecidableFalse
  refine ⟨S, hSfin, ⟨a⟩, G, hGdec, (fun _ => a), ?_, ?_⟩
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro y hybox htri; exact absurd htri (hno y hybox)


theorem bc112_separatedArmGraph_of_full (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc106_SeparatedContractedTrifGraph ω L R) : bc112_SeparatedArmGraph ω L R := by
  obtain ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hmin, hιinj, hleaf⟩ := h
  exact ⟨S, hSfin, hSne, G, hGdec, ιU, hnbr, hιinj⟩


theorem bc112_separatedArmGraph_of_bc103 (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc103_ContractedTrifGraph ω L R) : bc112_SeparatedArmGraph ω L R :=
  bc112_separatedArmGraph_of_full ω L R (bc106_separatedContractedTrifGraph_of_bc103 ω L R h)


open Classical in


theorem bc106_separatedContracted_of_gap1_gap2
    (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {S : Set (Site d)} (hSfin : Fintype (↑S : Type)) (hSne : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (hGdec : DecidableRel G.Adj)
    (hFdec : DecidableRel (osf_spanForest G).Adj) (ιU : Site d → (↑S : Type))
    
    (hnbr : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y →
      ∃ v₁ v₂ v₃ : (↑S : Type),
        G.Adj (ιU y) v₁ ∧ G.Adj (ιU y) v₂ ∧ G.Adj (ιU y) v₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₂ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₁ v₃ ∧
        ¬ (G.deleteIncidenceSet (ιU y)).Reachable v₂ v₃)
    
    (hιinj : ∀ y, y ∈ box d R → bc106_SeparatedCoarseTrif ω L y → ∀ z, z ∈ box d R →
      bc106_SeparatedCoarseTrif ω L z → ιU y = ιU z → y = z)
    
    (hmin : ∀ v, 1 ≤ (osf_spanForest G).degree v)
    
    (hleaf : ∀ v : (↑S : Type), (osf_spanForest G).degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
    bc106_SeparatedContractedTrifGraph ω L R :=
  ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hmin, hιinj, hleaf⟩


end StatMech.Walls
