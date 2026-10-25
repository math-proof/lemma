/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part4
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_step3MaskMatches (T : MonotoneAutomaton d)
    (D N : ℕ) (M : Finset (Site d)) :
    MeasurableSet {q : FieldTriple d | step3MaskMatches T D N M q} := by
  have heq : {q : FieldTriple d | step3MaskMatches T D N M q} =
      ⋂ z : Site d, if z ∈ M then
        if z ∈ boxFinsetBK d N then
          ⋃ a : Site d, if l1dist d a z < D then
            (zeroHighPair T M) ⁻¹'
              {omega | a ∈ pairLowInfiniteVertices omega}
          else ∅
        else ∅
      else
        if z ∈ boxFinsetBK d N then
          (⋃ a : Site d, if l1dist d a z < D then
            (zeroHighPair T M) ⁻¹'
              {omega | a ∈ pairLowInfiniteVertices omega}
          else ∅)ᶜ
        else Set.univ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    unfold step3MaskMatches
    apply forall_congr'
    intro z
    by_cases hzM : z ∈ M
    · by_cases hzN : z ∈ boxFinsetBK d N
      · simp [hzM, hzN]
        aesop
      · simp [hzM, hzN]
    · by_cases hzN : z ∈ boxFinsetBK d N
      · simp [hzM, hzN]
        constructor
        · intro h i hi hmem
          exact (Nat.not_lt_of_ge (h i hmem)) hi
        · intro h x hx
          exact Nat.le_of_not_gt (fun hlt => h x hlt hx)
      · simp [hzM, hzN]
  rw [heq]
  apply MeasurableSet.iInter
  intro z
  split_ifs
  all_goals first
    | exact MeasurableSet.empty
    | exact MeasurableSet.univ
    | apply MeasurableSet.iUnion; intro a; split_ifs
      · exact (measurable_zeroHighPair T M)
          (measurableSet_pairLowInfinite a)
      · exact MeasurableSet.empty
    | apply MeasurableSet.compl; apply MeasurableSet.iUnion; intro a; split_ifs
      · exact (measurable_zeroHighPair T M)
          (measurableSet_pairLowInfinite a)
      · exact MeasurableSet.empty


end StatMech.FrontierA
