/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcaconcreteclose
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Instance.StatisticalMechanics.Code.Walls.briraysintree
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


theorem bri_twoHub_witness :
    bri_twoHub.IsTree ∧ bri_twoHub.IsAcyclic ∧
    bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧ bri_twoHub.degree 4 = 2 ∧
    bri_twoHub.degree 2 = 1 ∧ bri_twoHub.degree 3 = 1 ∧
    bri_twoHub.degree 5 = 1 ∧ bri_twoHub.degree 6 = 1 ∧
    (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v) := by
  have htree : bri_twoHub.IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨by decide, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    decide
  refine ⟨htree, bau_isAcyclic_of_le_tree htree le_rfl, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, ?_⟩
  intro v hv; fin_cases v <;> first | (exfalso; exact hv (by decide)) | decide


theorem bri_twoHub_count :
    ({0, 1} : Finset (Fin 7)).card ≤ ({2, 3, 5, 6} : Finset (Fin 7)).card := by decide

#check @bri_rayGraph_le
#check @bri_union_le_acyclic
#check bri_twoHub_witness


theorem bri_bk_of_subforestData (p : NNReal) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bau_bk_of_subforestData p hp1 hp0 hdata


theorem bri_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bca_datum_implies_count ω L R h


theorem bri_status :
    
    (∀ (T : SimpleGraph (Site 2)) [LocallyFinite T], T ≤ hypercubicLattice 2 →
      ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R →
        (ray34_AvoidCluster T {x} w).Infinite →
        ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
          (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧
          (∃ k, r k ∈ vertexBoundary 2 R)) ∧
    
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    
    (bri_twoHub.IsTree ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧
      bri_twoHub.degree 4 = 2 ∧
      (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    
    (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T _ hle w x R hR hwx hw hinf
    exact bri_branchRay_reaches_boundary T hle hR hwx hw hinf
  · intro V T hT ι Gs hGs; exact bri_union_le_acyclic hT Gs hGs
  · exact ⟨bri_twoHub_witness.1, bri_twoHub_witness.2.2.1, bri_twoHub_witness.2.2.2.1,
      bri_twoHub_witness.2.2.2.2.1, bri_twoHub_witness.2.2.2.2.2.2.2.2.2⟩
  · intro ω L R h; exact bri_datum_implies_count ω L R h
  · intro p hp1 hp0 hdata; exact bri_bk_of_subforestData p hp1 hp0 hdata

end StatMech.Walls
