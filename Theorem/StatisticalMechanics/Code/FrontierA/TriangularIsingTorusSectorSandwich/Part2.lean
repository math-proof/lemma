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
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich


namespace StatMech.FrontierA

open StatMech.Ising


theorem triangularTorusEvenSubgraphSum_normalizedLog_gap_tendsto_zero
    (weight : (L : Nat) -> Sym2 (ZMod L × ZMod L) -> Real)
    (hweight : forall L edge, 0 <= weight L edge) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusEvenSubgraphSequence weight n) -
          Real.log (arfSectorNormMax
            (triangularTorusSectorSequence weight n))) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
  have hbounds (n : Nat) :
      0 <=
          (Real.log (triangularTorusEvenSubgraphSequence weight n) -
            Real.log (arfSectorNormMax
              (triangularTorusSectorSequence weight n))) /
            (n + 3 : Real) ^ 2 /\
        (Real.log (triangularTorusEvenSubgraphSequence weight n) -
            Real.log (arfSectorNormMax
              (triangularTorusSectorSequence weight n))) /
            (n + 3 : Real) ^ 2 <= Real.log 2 / (n + 3 : Real) ^ 2 := by
    let L := n + 3
    letI : Fact (2 < L) := ⟨by dsimp [L]; omega⟩
    simpa [L, triangularTorusEvenSubgraphSequence,
      triangularTorusSectorSequence] using
        triangularTorusEvenSubgraphSum_normalizedLog_gap_le
          L (weight L) (hweight L)
  have hrecip : Filter.Tendsto
      (fun n : Nat => (1 : Real) / (n + 3 : Real))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := Real)).comp
        (Filter.tendsto_add_atTop_nat 3)
  have hupper : Filter.Tendsto
      (fun n : Nat => Real.log 2 / (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).mul
        (hrecip.mul hrecip)
    simpa [div_eq_mul_inv, pow_two] using h
  apply squeeze_zero'
    (f := fun n : Nat =>
      (Real.log (triangularTorusEvenSubgraphSequence weight n) -
        Real.log (arfSectorNormMax
          (triangularTorusSectorSequence weight n))) /
        (n + 3 : Real) ^ 2)
    (g := fun n : Nat => Real.log 2 / (n + 3 : Real) ^ 2)
  · exact Filter.Eventually.of_forall fun n => (hbounds n).1
  · exact Filter.Eventually.of_forall fun n => (hbounds n).2
  · exact hupper

end StatMech.FrontierA
