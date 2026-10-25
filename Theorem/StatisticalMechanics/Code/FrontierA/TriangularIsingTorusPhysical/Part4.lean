/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusShiftedAssembly
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part3
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularTorusIsingPartitionSequence_eq
    (J1 J2 J3 : Real) (n : Nat) :
    triangularTorusIsingPartitionSequence J1 J2 J3 n =
      2 ^ ((n + 3) * (n + 3)) *
        triangularTorusNormalizedEvenSequence J1 J2 J3 n := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  rw [triangularTorusIsingPartitionSequence,
    triangularTorusIsingPartition_highTemperature]
  rw [prod_cosh_triangularTorusRealEdgeWeight]
  have hcard : Fintype.card (ZMod L × ZMod L) = L * L := by
    simp [Fintype.card_prod, ZMod.card]
  rw [hcard]
  simp only [triangularTorusNormalizedEvenSequence]
  have htanh :
      (fun edge => Real.tanh
        (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) =
        triangularTorusRealEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) := by
    funext edge
    unfold triangularTorusRealEdgeWeight
    split_ifs <;> rfl
  rw [htanh]
  ring


theorem triangularTorusIsingPartition_freeEnergy_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hJ1 : 0 ≤ J1) (hJ2 : 0 ≤ J2) (hJ3 : 0 ≤ J3)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
  have heven := triangularTorusNormalizedEven_logDensity_tendsto
    J1 J2 J3 rho hrho hJ1 hJ2 hJ3 hpos
  have hlog2 : Filter.Tendsto
      (fun n : Nat =>
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (Real.log 2)) := by
    have heq : ∀ n : Nat,
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
            (n + 3 : Real) ^ 2 = Real.log 2 := by
      intro n
      rw [Real.log_pow]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      field_simp
    exact (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).congr'
        (Filter.Eventually.of_forall fun n => (heq n).symm)
  have hsum := hlog2.add heven
  have hneg := hsum.neg
  have hneg' : Filter.Tendsto
      (fun (x : Nat) =>
        -(Real.log (2 ^ ((x + 3) * (x + 3)) : Real) /
            (x + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 x) /
            (x + 3 : Real) ^ 2))
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
    convert hneg using 1 <;> unfold triangularIsingFreeEnergyValue <;> ring
  apply hneg'.congr'
  filter_upwards [] with n
  rw [triangularTorusIsingPartitionSequence_eq]
  have htwo : (2 ^ ((n + 3) * (n + 3)) : Real) ≠ 0 := by positivity
  have hevenPos : 0 < triangularTorusNormalizedEvenSequence
      J1 J2 J3 n := by
    let L := n + 3
    letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
    unfold triangularTorusNormalizedEvenSequence
    exact mul_pos (by positivity)
      (inhomogeneousEvenSubgraphSum_pos_of_nonneg
        (triangularTorusGraph L)
        (triangularTorusRealEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) (by
            intro edge
            unfold triangularTorusRealEdgeWeight
            split_ifs <;> exact real_tanh_nonneg (by assumption)))
  rw [Real.log_mul htwo hevenPos.ne']
  ring

end StatMech.FrontierA
