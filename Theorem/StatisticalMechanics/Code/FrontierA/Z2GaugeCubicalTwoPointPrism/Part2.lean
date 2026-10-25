/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalTwoPointPrism


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech StatMech.Ising

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]

theorem typedSpinProduct_oddCubical_eq_prismSpinProduct
    (n : Nat)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none)
    (q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)) :
    typedSpinProduct s.1 (some q) (some r) =
      rectangularPrismSpin (oddCubicalAnchoredEquivPrismConfig n s)
          (oddCubicalCellEquivPrismSite n q).x
          (oddCubicalCellEquivPrismSite n q).y
          (oddCubicalCellEquivPrismSite n q).z *
        rectangularPrismSpin (oddCubicalAnchoredEquivPrismConfig n s)
          (oddCubicalCellEquivPrismSite n r).x
          (oddCubicalCellEquivPrismSite n r).y
          (oddCubicalCellEquivPrismSite n r).z := by
  cases hq : s.1 (some q) <;> cases hr : s.1 (some r) <;>
    simp [typedSpinProduct, rectangularPrismSpin, spin,
      oddCubicalAnchoredEquivPrismConfig, oddCubicalCellEquivPrismSite,
      hq, hr]

theorem oddCubicalAnchoredWeight_eq_plusPrismWeight
    (J beta : Real) (n : Nat)
    (s : AnchoredConfig
      (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none) :
    multibondIsingWeight cubicalDualEnds (fun _ => beta * J) s.1 =
      Real.exp (-beta * rectangularPrismPlusEnergy J
        (oddCubicalAnchoredEquivPrismConfig n s)) := by
  unfold multibondIsingWeight
  rw [sum_oddCubicalDualAgreement_eq_plusPrismInteraction]
  unfold rectangularPrismPlusEnergy
  congr 1
  ring


theorem oddCubicalDualTwoPoint_eq_plusPrismTwoPoint
    (J beta : Real) (n : Nat)
    (q r : CubicalCell (2 * n + 1) (2 * n + 1) (2 * n + 1)) :
    multibondIsingTwoPoint
        (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1)
          (c := 2 * n + 1))
        (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) =>
          beta * J)
        (some q) (some r) =
      oddPrismPlusTwoPoint J beta n
        (oddCubicalCellEquivPrismSite n q)
        (oddCubicalCellEquivPrismSite n r) := by
  unfold multibondIsingTwoPoint oddPrismPlusTwoPoint
  rw [multibondIsingTwoPointNumerator_eq_two_mul_anchored none]
  rw [oddCubicalDualPartition_eq_two_mul_plusPrismPartition]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : Real) ≠ 0)]
  rw [← Equiv.sum_comp (oddCubicalAnchoredEquivPrismConfig n)]
  apply congrArg (fun z : Real => z /
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n)
  apply Finset.sum_congr rfl
  intro s _
  rw [oddCubicalAnchoredWeight_eq_plusPrismWeight,
    typedSpinProduct_oddCubical_eq_prismSpinProduct]

end
end StatMech.FrontierA
