/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceFactor
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]

noncomputable def independentMixedOrConfigLaw
    (rho nu : ProbabilityMeasure (ConfigSpace E)) :
    ProbabilityMeasure (ConfigSpace E) :=
  (independentMixedPairConfigLaw rho nu).map
    measurable_pairOrConfig.aemeasurable

end StatMech.FrontierB
