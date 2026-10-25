/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def shb_fullWeightMass (β : ℝ) (J : Sym2 V → ℝ) : ℝ :=
  ∑' m : G.edgeFinset → ℕ, weight G β J (ofEdgeFun G m)

noncomputable def shb_cutLeftMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' a, shb_cutLeftWeight G β J P a

noncomputable def shb_cutRightMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' b, shb_cutRightWeight G β J P b

noncomputable def shb_cutJoinMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' ab, shb_cutJoinWeight G β J P ab

end StatMech.Sharpness
