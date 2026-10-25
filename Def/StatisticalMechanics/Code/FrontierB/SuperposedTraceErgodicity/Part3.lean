/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part2
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


noncomputable def independentPairConfigLaw
    (rho : ProbabilityMeasure (ConfigSpace E)) :
    ProbabilityMeasure (ConfigSpace (E ⊕ E)) :=
  (rho.prod rho).map measurable_pairConfig.aemeasurable


def pairLeft [DecidableEq E] (T : Finset (E ⊕ E)) : Finset E :=
  T.biUnion fun z => match z with
    | Sum.inl e => {e}
    | Sum.inr _ => ∅


def pairRight [DecidableEq E] (T : Finset (E ⊕ E)) : Finset E :=
  T.biUnion fun z => match z with
    | Sum.inl _ => ∅
    | Sum.inr e => {e}

end StatMech.FrontierB
