/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Def.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part2
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem measurable_pairConfig : Measurable
    (Function.uncurry pairConfig :
      ConfigSpace E × ConfigSpace E -> ConfigSpace (E ⊕ E)) := by
  rw [measurable_pi_iff]
  intro z
  cases z with
  | inl e => exact (measurable_pi_apply e).comp measurable_fst
  | inr e => exact (measurable_pi_apply e).comp measurable_snd

theorem pairConfig_shift (g : H) (omega eta : ConfigSpace E) :
    pairConfig (shift g omega) (shift g eta) =
      shift g (pairConfig omega eta) := by
  funext z
  cases z <;> rfl


end StatMech.FrontierB
