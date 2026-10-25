/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech StatMech.Ising

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]

theorem typedSpinProduct_unanchorConfig (root x y : V) (b : Bool)
    (s : AnchoredConfig V root) :
    typedSpinProduct (unanchorConfig b s) x y =
      typedSpinProduct s.1 x y := by
  cases hx : s.1 x <;> cases hy : s.1 y <;> cases b <;>
    simp [typedSpinProduct, unanchorConfig, hx, hy]


theorem multibondIsingTwoPointNumerator_eq_two_mul_anchored
    (root : V) (ends : P -> V × V) (J : P -> Real) (x y : V) :
    (∑ sigma : V -> Bool,
        multibondIsingWeight ends J sigma * typedSpinProduct sigma x y) =
      2 * ∑ s : AnchoredConfig V root,
        multibondIsingWeight ends J s.1 * typedSpinProduct s.1 x y := by
  calc
    (∑ sigma : V -> Bool,
        multibondIsingWeight ends J sigma * typedSpinProduct sigma x y) =
        ∑ bs : Bool × AnchoredConfig V root,
          multibondIsingWeight ends J (unanchorConfig bs.1 bs.2) *
            typedSpinProduct (unanchorConfig bs.1 bs.2) x y := by
      apply Fintype.sum_equiv (configEquivBoolAnchored root)
      intro sigma
      rw [show unanchorConfig ((configEquivBoolAnchored root sigma).1)
          ((configEquivBoolAnchored root sigma).2) = sigma from
        (configEquivBoolAnchored root).left_inv sigma]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [multibondIsingWeight_eq_activity,
        multibondCut_unanchorConfig, typedSpinProduct_unanchorConfig]
      rw [Fintype.sum_bool]
      ring


end
end StatMech.FrontierA
