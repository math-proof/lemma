/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSectorSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectors.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingArfSandwich
import Mathlib.Analysis.SpecificLimits.Basic


namespace StatMech.FrontierA

open StatMech.Ising


theorem inhomogeneousEvenSubgraphSum_pos_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V -> Real) (hweight : forall edge, 0 <= weight edge) :
    0 < inhomogeneousEvenSubgraphSum G weight := by
  classical
  have hempty : (∅ : Finset (Sym2 V)) ∈ evenSubgraphs G := by
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, isEvenSubgraph_empty⟩
  have hnonneg (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs G) :
      0 <= ∏ edge ∈ F, weight edge := by
    exact Finset.prod_nonneg fun edge hedge => hweight edge
  have hsingle := Finset.single_le_sum hnonneg hempty
  simpa [inhomogeneousEvenSubgraphSum] using
    (show (0 : Real) < 1 from zero_lt_one).trans_le hsingle


theorem triangularTorusEvenSubgraphSum_log_sandwich
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) -> Real)
    (hweight : forall edge, 0 <= weight edge) :
    let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
      triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b
    Real.log (arfSectorNormMax sector) <=
        Real.log (inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) /\
      Real.log (inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) <=
        Real.log (arfSectorNormMax sector) + Real.log 2 := by
  dsimp only
  apply arfSector_log_sandwich
  · exact inhomogeneousEvenSubgraphSum_pos_of_nonneg
      (triangularTorusGraph L) weight hweight
  · intro a b
    exact triangularTorusWeightedSpin_norm_le_evenSubgraphSum
      L hweight a b
  · simpa using two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight


theorem triangularTorusEvenSubgraphSum_normalizedLog_gap_le
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) -> Real)
    (hweight : forall edge, 0 <= weight edge) :
    let sector : Fin 2 -> Fin 2 -> Complex := fun a b =>
      triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b
    let partition :=
      inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight
    0 <= (Real.log partition - Real.log (arfSectorNormMax sector)) /
        (L : Real) ^ 2 /\
      (Real.log partition - Real.log (arfSectorNormMax sector)) /
          (L : Real) ^ 2 <= Real.log 2 / (L : Real) ^ 2 := by
  dsimp only
  have hs := triangularTorusEvenSubgraphSum_log_sandwich L weight hweight
  have hL : 0 < (L : Real) := by
    have hLnat : 0 < L := lt_trans (by omega) (Fact.out : 2 < L)
    exact_mod_cast hLnat
  have hden : 0 < (L : Real) ^ 2 := sq_pos_of_pos hL
  constructor
  · exact div_nonneg (sub_nonneg.mpr hs.1) hden.le
  · exact div_le_div_of_nonneg_right (by linarith [hs.2]) hden.le

end StatMech.FrontierA
