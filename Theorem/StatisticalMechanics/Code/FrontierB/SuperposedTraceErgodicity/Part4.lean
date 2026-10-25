/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Def.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part4
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem measurable_pairOrConfig :
    Measurable (pairOrConfig : ConfigSpace (E ⊕ E) -> ConfigSpace E) := by
  apply Continuous.measurable
  refine continuous_pi fun e => ?_
  have hor : Continuous (fun p : Bool × Bool => p.1 || p.2) :=
    continuous_of_discreteTopology
  have hpair : Continuous (fun omega : ConfigSpace (E ⊕ E) =>
      (omega (Sum.inl e), omega (Sum.inr e))) :=
    (continuous_apply (Sum.inl e)).prodMk
      (continuous_apply (Sum.inr e))
  exact hor.comp hpair

theorem pairOrConfig_shift (g : H) : Function.Semiconj
    (pairOrConfig : ConfigSpace (E ⊕ E) -> ConfigSpace E)
    (shift g) (shift g) := by
  intro omega
  rfl


end StatMech.FrontierB
