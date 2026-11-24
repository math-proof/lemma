module
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentAfterMixing
public import Theorem.StatisticalMechanics.Code.FrontierB.PlusAxisMixing
public import Theorem.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part5
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCoarseUniqueness
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPersistence
public import Theorem.StatisticalMechanics.Code.FK.PairMixingGenMixing
public import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


noncomputable def independentMixedPairConfigLaw
    (rho nu : ProbabilityMeasure (ConfigSpace E)) :
    ProbabilityMeasure (ConfigSpace (E ⊕ E)) :=
  (rho.prod nu).map measurable_pairConfig.aemeasurable

end StatMech.FrontierB
