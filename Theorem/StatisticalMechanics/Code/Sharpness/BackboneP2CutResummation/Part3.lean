/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part3
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem shb_fullWeightMass_eq_cutJoinMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_fullWeightMass G β J = shb_cutJoinMass G β J P := by
  unfold shb_fullWeightMass shb_cutJoinMass shb_cutJoinWeight shb_cutJoin
  rw [← (shb_cutEquiv G P).symm.tsum_eq]

theorem shb_cutJoinMass_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_cutJoinMass G β J P =
      shb_cutLeftMass G β J P * shb_cutRightMass G β J P := by
  unfold shb_cutJoinMass shb_cutLeftMass shb_cutRightMass
  rw [tsum_congr (fun ab => shb_cutJoinWeight_factor G β J P ab)]
  exact shb_tsum_prod_factor
    (shb_cutLeftWeight G β J P) (shb_cutRightWeight G β J P)
    (shb_summable_weight_cutLeft G β J P)
    (shb_summable_weight_cutRight G β J P)


theorem shb_tsum_weight_cut_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_fullWeightMass G β J =
      shb_cutLeftMass G β J P * shb_cutRightMass G β J P :=
  (shb_fullWeightMass_eq_cutJoinMass G β J P).trans
    (shb_cutJoinMass_factor G β J P)

end StatMech.Sharpness
