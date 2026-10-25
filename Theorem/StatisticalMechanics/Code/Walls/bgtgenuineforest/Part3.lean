/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.btrtrifnotion.Part3
import Def.StatisticalMechanics.Code.Walls.bgtgenuineforest.Part2
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


theorem bgt_genuineForest_imp_noBnd (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bgt_GenuineForest ω L R) :
    bgt_GenuineForestNoBnd ω L R (boxSV_boundaryCard d R) := by
  classical
  obtain ⟨W, hWf, hWne, hWde, G, hGdr, ιT, lamL, hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  exact ⟨W, hWf, hWne, hWde, G, hGdr, ιT, hacyc, hmin, hdeg3, hιinj,
    flc2_leaf_card_le_boundary G R lamL hlammap hlaminj⟩


theorem bgt_genuineTcount_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bgt_GenuineForest ω L R) :
    (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  bgt_genuineTcount_le_leafCard ω L R _ (bgt_genuineForest_imp_noBnd ω L R h)


open Classical in


theorem bgt_genuineForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) :
    bgt_GenuineForest ω L R := by
  classical
  refine ⟨Fin 2, inferInstance, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun _ => (0 : Fin 2)), (fun v => if v = 0 then z₀ else z₁),
    Flc2Witness.pathG_isTree.isAcyclic, (fun v => (Flc2Witness.pathG_deg v).ge), ?_, ?_, ?_, ?_⟩
  · intro y hybox hgen; exact absurd hgen (hno y hybox)
  · intro y hybox hgen; exact absurd hgen (hno y hybox)
  · intro v _; fin_cases v
    · simpa using hz₀
    · simpa using hz₁
  · intro u hu v hv huv
    fin_cases u <;> fin_cases v
    · rfl
    · exact absurd huv hzne
    · exact absurd huv.symm hzne
    · rfl


theorem bgt_bc60_genuineForest (L R : ℕ)
    {z₀ z₁ : Site 2} (hz₀ : z₀ ∈ vertexBoundary 2 R) (hz₁ : z₁ ∈ vertexBoundary 2 R)
    (hzne : z₀ ≠ z₁) :
    bgt_GenuineForest bc60_upperLines L R :=
  bgt_genuineForest_of_noTrif bc60_upperLines L R hz₀ hz₁ hzne
    (fun y _ => btr_bc60_not_genuineTrif L y)


theorem bgt_bc60_genuineTcount_zero (L R : ℕ) :
    (btr_genuineTrifFinset bc60_upperLines L R).card = 0 :=
  btr_bc60_genuineTcount_zero L R


theorem bgt_status (hd : 1 ≤ d) :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bgt_GenuineForest ω L R →
      (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R m : ℕ), bgt_GenuineForestNoBnd ω L R m →
      (btr_genuineTrifFinset ω L R).card ≤ m) ∧
    
    (∀ (L R : ℕ), (btr_genuineTrifFinset bc60_upperLines L R).card = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) → bgt_GenuineForest ω L R) := by
  refine ⟨fun ω L R h => bgt_genuineTcount_le_boundary ω L R h,
    fun ω L R m h => bgt_genuineTcount_le_leafCard ω L R m h,
    fun L R => bgt_bc60_genuineTcount_zero L R, ?_⟩
  intro ω L R z₀ z₁ hz₀ hz₁ hzne hno
  exact bgt_genuineForest_of_noTrif ω L R hz₀ hz₁ hzne hno

end StatMech.Walls
