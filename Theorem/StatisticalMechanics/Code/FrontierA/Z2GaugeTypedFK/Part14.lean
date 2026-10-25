/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part16
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem exp_mul_typedES_spinProduct_sum_omega
    (ends : P -> V × V) (J : P -> Real) (sigma : V -> Bool)
    (x y : V) :
    Real.exp (∑ p : P, J p) *
        (∑ omega : P -> Bool,
          typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅
            sigma omega * typedSpinProduct sigma x y) =
      multibondIsingWeight ends J sigma * typedSpinProduct sigma x y := by
  rw [← Finset.sum_mul]
  rw [typedESWeight_sum_omega_eq_shiftedCut]
  have hempty : multibondCut ends sigma ∆ (∅ : Finset P) =
      multibondCut ends sigma := by
    ext p
    simp [Finset.mem_symmDiff]
  rw [hempty]
  rw [multibondIsingWeight_eq_activity]
  ring

theorem exp_mul_typedES_twoPointNumerator
    (ends : P -> V × V) (J : P -> Real) (x y : V) :
    Real.exp (∑ p : P, J p) *
        (∑ omega : P -> Bool, ∑ sigma : V -> Bool,
          typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅
            sigma omega * typedSpinProduct sigma x y) =
      ∑ sigma : V -> Bool,
        multibondIsingWeight ends J sigma * typedSpinProduct sigma x y := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  exact exp_mul_typedES_spinProduct_sum_omega ends J sigma x y


theorem typedESTwoPoint_coupling_eq_multibondIsingTwoPoint
    (ends : P -> V × V) (J : P -> Real) (x y : V) :
    typedESTwoPoint ends (fun p => 1 - Real.exp (-2 * J p)) x y =
      multibondIsingTwoPoint ends J x y := by
  unfold typedESTwoPoint multibondIsingTwoPoint
  let e := Real.exp (∑ p : P, J p)
  let A := ∑ omega : P -> Bool, ∑ sigma : V -> Bool,
    typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅ sigma omega *
      typedSpinProduct sigma x y
  let B := typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) ∅
  let C := ∑ sigma : V -> Bool,
    multibondIsingWeight ends J sigma * typedSpinProduct sigma x y
  let D := multibondIsingPartition ends J
  have hnum : e * A = C :=
    exp_mul_typedES_twoPointNumerator ends J x y
  have hden : e * B = D :=
    by
      have hpart :=
        multibondIsingPartition_twist_eq_exp_mul_typedESZ ends J ∅
      have htwist : multibondTwistCoupling J (∅ : Finset P) = J := by
        funext p
        simp [multibondTwistCoupling]
      rw [htwist] at hpart
      exact hpart.symm
  change A / B = C / D
  rw [← hnum, ← hden]
  exact (mul_div_mul_left (c := e) A B (by simp [e])).symm


theorem typedFKTwoPoint_eq_multibondIsingTwoPoint
    (ends : P -> V × V) (J : P -> Real) (x y : V) :
    typedFKTwoPoint ends (fun p => 1 - Real.exp (-2 * J p)) x y =
      multibondIsingTwoPoint ends J x y := by
  rw [← typedESTwoPoint_eq_typedFKTwoPoint]
  exact typedESTwoPoint_coupling_eq_multibondIsingTwoPoint ends J x y

end
end StatMech.FrontierA
