/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part4
import Def.StatisticalMechanics.Code.Walls.bcvcutvertex.Part2
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


theorem bcv_globalForest_of_treeData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bcv_ClusterTreeData ω L R) : bc69_Gn_globalForest ω L R := by
  obtain ⟨S, hSfin, hSne, H, T, hTdec, ιU, hTH, hT, hmin, hsep, hιinj, hleaf⟩ := h
  refine ⟨S, hSfin, hSne, T, hTdec, ιU, hT.isAcyclic, hmin, ?_, hιinj, hleaf⟩
  
  intro y hybox htri
  obtain ⟨v₁, v₂, v₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := hsep y hybox htri
  exact bcv_trif_degree_ge_three hTH hT.connected hn₁ hn₂ hn₃ hs₁₂ hs₁₃ hs₂₃


theorem bcv_count_of_treeData (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bcv_ClusterTreeData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bc69_count_via_leafBound ω L R (bcv_globalForest_of_treeData ω L R h)


theorem bcv_bk_of_treeData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
  apply bgn_bk_of_forest p hp1 hp0
  intro ω L R
  rw [bgn_forest_iff_bc69]
  exact bcv_globalForest_of_treeData ω L R (hdata ω L R)


theorem bcv_status :
    
    (∀ {V : Type} [Fintype V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T ≤ H → T.Connected → ∀ (x : V) {k : ℕ} (a : Fin k → V), (∀ i, a i ≠ x) →
      (∀ i j, i ≠ j → ¬ (bkg_deleteVertex H x).Reachable (a i) (a j)) → k ≤ T.degree x) ∧
    
    (∀ {V : Type} [Fintype V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj],
      T ≤ H → T.Connected → ∀ {x a₁ a₂ a₃ : V}, a₁ ≠ x → a₂ ≠ x → a₃ ≠ x →
      ¬ (bkg_deleteVertex H x).Reachable a₁ a₂ → ¬ (bkg_deleteVertex H x).Reachable a₁ a₃ →
      ¬ (bkg_deleteVertex H x).Reachable a₂ a₃ → 3 ≤ T.degree x) ∧
    
    (∀ {T : SimpleGraph (Fin 8)} [_i : DecidableRel T.Adj], T ≤ bgn_W → T.Connected →
      3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bcv_ClusterTreeData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V _ H T _ hTH hTconn x k a hne hsep
    exact bcv_degree_ge_components hTH hTconn x a hne hsep
  · intro V _ H T _ hTH hTconn x a₁ a₂ a₃ h₁ h₂ h₃ hs₁₂ hs₁₃ hs₂₃
    exact bcv_trif_degree_ge_three hTH hTconn h₁ h₂ h₃ hs₁₂ hs₁₃ hs₂₃
  · intro T _ hTH hTconn
    exact bcv_bgnW_test hTH hTconn
  · intro ω L R h
    exact bcv_count_of_treeData ω L R h

end StatMech.Walls
