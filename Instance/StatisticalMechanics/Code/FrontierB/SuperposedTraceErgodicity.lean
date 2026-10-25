/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


instance sumMulAction : MulAction H (E ⊕ E) where
  smul g z := match z with
    | Sum.inl e => Sum.inl (g • e)
    | Sum.inr e => Sum.inr (g • e)
  one_smul z := by
    cases z with
    | inl e => exact congrArg Sum.inl (one_smul H e)
    | inr e => exact congrArg Sum.inr (one_smul H e)
  mul_smul g h z := by
    cases z with
    | inl e => exact congrArg Sum.inl (mul_smul g h e)
    | inr e => exact congrArg Sum.inr (mul_smul g h e)


end StatMech.FrontierB
