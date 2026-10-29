/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bof2leafcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Instance.StatisticalMechanics.Code.Walls.bof2leafcount.Part2
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


theorem bof2_interiorLeaf_witness :
    bof2_advT ≤ bof2_advG ∧
    bof2_advG.degree 2 = 2 ∧          
    bof2_advT.degree 2 = 1 ∧          
    (2 : Fin 4) ∉ ({0} : Finset (Fin 4)) := by  
  refine ⟨?_, by decide, by decide, by decide⟩
  change ∀ a b, bof2_advT.Adj a b → bof2_advG.Adj a b; decide


theorem bof2_interiorLeaf_obstruction :
    ∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
      (B : Finset (Fin 4)),
      T ≤ G ∧ T.IsTree ∧
      (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
      ¬ (∀ v, T.degree v = 1 → v ∈ B) := by
  refine ⟨bof2_advG, bof2_advT, inferInstance, inferInstance, {0}, ?_, ?_,
    ⟨2, by decide, by decide, by decide⟩, ?_⟩
  · change ∀ a b, bof2_advT.Adj a b → bof2_advG.Adj a b; decide
  · rw [isTree_iff_connected_and_card]
    refine ⟨by decide, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  · intro hall
    have := hall 2 (by decide)
    revert this; decide


theorem bof2_bk_of_treeData (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bcv_bk_of_treeData p hp1 hp0 hdata


theorem bof2_status :
    
    (∀ {V : Type} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T.IsTree →
      (Finset.univ.filter (fun v => 3 ≤ T.degree v)).card ≤
        (Finset.univ.filter (fun v => T.degree v = 1)).card) ∧
    
    (∀ {V : Type} [Fintype V] [DecidableEq V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T ≤ H → T.IsTree → ∀ {ι : Type} [Fintype ι] (f : ι → V), Function.Injective f →
      (∀ i, ∃ a₁ a₂ a₃ : V, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₂ ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₁ a₃ ∧
        ¬ (bkg_deleteVertex H (f i)).Reachable a₂ a₃) →
      ∀ (B : Finset V), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧
    
    (∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj)
      (B : Finset (Fin 4)),
      T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧
      ¬ (∀ v, T.degree v = 1 → v ∈ B)) ∧
    
    (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V _ _ T _ hT; exact bof2_forest_handshake hT
  · intro V _ _ H T _ hTH hT ι _ f hf hcut B hleaf
    exact bof2_trifCount_le_boundary hTH hT f hf hcut B hleaf
  · exact bof2_interiorLeaf_obstruction
  · intro p hp1 hp0 hdata; exact bof2_bk_of_treeData p hp1 hp0 hdata

end StatMech.Walls
