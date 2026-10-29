/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bauacyclicarm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.blfboundaryleaf.Part3
import Instance.StatisticalMechanics.Code.Walls.bauacyclicarm.Part2
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


theorem bau_sub_witness :
    bau_sub ≤ bau_star ∧ bau_sub ≠ bau_star ∧ bau_sub.IsAcyclic := by
  have hle : bau_sub ≤ bau_star := by
    change ∀ a b, bau_sub.Adj a b → bau_star.Adj a b; decide
  refine ⟨hle, ?_, ?_⟩
  · intro h
    have : bau_star.Adj 0 3 := by decide
    rw [← h] at this
    exact absurd this (by decide)
  · exact bau_isAcyclic_of_le_tree bau_star_witness.1 hle


theorem bau_status :
    
    (∀ {V : Type} {T G : SimpleGraph V}, T.IsTree → G ≤ T → G.IsAcyclic) ∧
    
    (∀ {V : Type} {H : SimpleGraph V}, H.Connected → ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → blf_AcyclicArmUnion ω L R) ∧
    
    (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    
    (bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V T G hT hle; exact bau_isAcyclic_of_le_tree hT hle
  · intro V H hH; exact bau_exists_spanningTree_infinite hH
  · intro ω L R h; exact bau_blf_of_subforestData ω L R h
  · intro p hp1 hp0 hdata; exact bau_bk_of_subforestData p hp1 hp0 hdata
  · exact ⟨bau_star_witness.1, bau_star_witness.2.1, bau_star_witness.2.2.1⟩

end StatMech.Walls
