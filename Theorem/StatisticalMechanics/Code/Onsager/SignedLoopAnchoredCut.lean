/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
open scoped BigOperators
open Finset


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {I P V : Type*}


theorem optionInteriorCutSum_eq_anchored
    [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]
    (ends : P → Option I × Option I) (observable : Finset P → Real) :
    (∑ tau : I → Bool,
      observable (multibondCut ends (ons_optionAnchoredEquiv tau).1)) =
      ∑ config : AnchoredConfig (Option I) none,
        observable (multibondCut ends config.1) := by
  rw [← (ons_optionAnchoredEquiv (I := I)).sum_comp]


theorem multibondCutSum_eq_two_mul_anchored
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (ends : P → V × V) (root : V) (observable : Finset P → Real) :
    (∑ config : V → Bool, observable (multibondCut ends config)) =
      2 * ∑ config : AnchoredConfig V root,
        observable (multibondCut ends config.1) := by
  calc
    (∑ config : V → Bool, observable (multibondCut ends config)) =
        ∑ state : Bool × AnchoredConfig V root,
          observable (multibondCut ends
            (unanchorConfig state.1 state.2)) := by
      apply Fintype.sum_equiv (configEquivBoolAnchored root)
      intro config
      rw [show unanchorConfig ((configEquivBoolAnchored root config).1)
          ((configEquivBoolAnchored root config).2) = config from
        (configEquivBoolAnchored root).left_inv config]
    _ = ∑ state : Bool × AnchoredConfig V root,
          observable (multibondCut ends state.2.1) := by
      apply Finset.sum_congr rfl
      intro state _
      rw [multibondCut_unanchorConfig]
    _ = _ := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      ring

end
end StatMech.Onsager
