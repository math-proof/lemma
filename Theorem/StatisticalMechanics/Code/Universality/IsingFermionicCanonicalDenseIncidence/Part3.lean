/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part3
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

theorem fkIsingDenseRationalPoint_denseRange :
    DenseRange fkIsingDenseRationalPoint := by
  have henum : DenseRange fkIsingRationalPairEnumeration :=
    fkIsingRationalPairEnumeration_surjective.denseRange
  have hcontinuous : Continuous fkIsingRationalComplex := by
    unfold fkIsingRationalComplex
    fun_prop
  simpa only [Function.comp_def, fkIsingDenseRationalPoint] using
    fkIsingRationalComplex_denseRange.comp henum hcontinuous

theorem int_natAbs_le_iff (x : Int) (n : Nat) :
    x.natAbs ≤ n ↔ -(n : Int) ≤ x ∧ x ≤ n := by
  rw [show x.natAbs ≤ n ↔ |x| ≤ (n : Int) by
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le.symm]
  exact abs_le


end
end StatMech.Universality
