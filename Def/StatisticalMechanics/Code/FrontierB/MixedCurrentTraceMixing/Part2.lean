/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentAfterMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusAxisMixing
import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCoarseUniqueness
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPersistence
import Theorem.StatisticalMechanics.Code.FK.PairMixingGenMixing
import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


noncomputable def independentMixedPairConfigLaw
    (rho nu : ProbabilityMeasure (ConfigSpace E)) :
    ProbabilityMeasure (ConfigSpace (E ⊕ E)) :=
  (rho.prod nu).map measurable_pairConfig.aemeasurable

end StatMech.FrontierB
