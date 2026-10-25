/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part3


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem reflectedRadialBilinearCellContour_eq
    (mesh : Real) (a00 a10 a01 a11 : Complex) :
    reflectedRadialBilinearCellContour mesh a00 a10 a01 a11 =
      (mesh : Complex) / 2 *
        ((a10 - a01) + Complex.I * (a11 - a00)) := by
  unfold reflectedRadialBilinearCellContour
  ring

theorem intervalIntegral_complexAffine_unit (a b : Complex) :
    (∫ x : Real in 0..1,
      ((1 - x : Real) : Complex) * a + (x : Complex) * b) =
      (a + b) / 2 := by
  let P : Real -> Complex := fun x =>
    ((x : Complex) - (x : Complex) ^ 2 / 2) * a +
      ((x : Complex) ^ 2 / 2) * b
  have hP : forall x : Real, HasDerivAt P
      (((1 - x : Real) : Complex) * a + (x : Complex) * b) x := by
    intro x
    have hx : HasDerivAt (fun y : Real => (y : Complex)) 1 x :=
      (hasDerivAt_id (x : Complex)).comp_ofReal
    dsimp only [P]
    convert ((hx.sub ((hx.pow 2).div_const 2)).mul_const a).add
      (((hx.pow 2).div_const 2).mul_const b) using 1
    all_goals
      push_cast
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => hP x)]
  · dsimp only [P]
    norm_num
    ring
  · exact (by fun_prop : Continuous (fun x : Real =>
      ((1 - x : Real) : Complex) * a + (x : Complex) * b)).intervalIntegrable 0 1


theorem complexDisplacementIntegral_eq_average_mul
    (f : Complex -> Complex) (a v A B : Complex)
    (haffine : ∀ t ∈ Set.Icc (0 : Real) 1,
      f (a + (t : Complex) * v) =
        ((1 - t : Real) : Complex) * A + (t : Complex) * B) :
    complexDisplacementIntegral f a v = (A + B) / 2 * v := by
  unfold complexDisplacementIntegral
  rw [intervalIntegral.integral_mul_const]
  congr 1
  rw [← intervalIntegral_complexAffine_unit A B]
  apply intervalIntegral.integral_congr
  intro t ht
  exact haffine t (by simpa [Set.uIcc_of_le zero_le_one] using ht)


end
end StatMech.Universality
