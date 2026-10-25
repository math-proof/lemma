/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/FKIsingInterfaceConvergenceReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Def.StatisticalMechanics.Code.SLE.ChainCapacity.Part2
import Theorem.StatisticalMechanics.Code.SLE.CardyCLE.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
open Filter MeasureTheory Set Topology


namespace StatMech.SLE

def IsWeaklySequentiallyPrecompact
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (laws : Nat -> ProbabilityMeasure X) : Prop :=
  forall phi : Nat -> Nat, StrictMono phi ->
    exists psi : Nat -> Nat, StrictMono psi /\
      exists limit : ProbabilityMeasure X,
        Tendsto (fun n => laws (phi (psi n))) atTop (nhds limit)


end StatMech.SLE
