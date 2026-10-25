/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusScalingHandoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open ProbabilityTheory

noncomputable section

def isingTorusFieldLaw {E : Type*} [MeasurableSpace E]
  (d k : Nat) (beta : Real)
    (X : ConfigSpace (IsingDyadicTorus d k) -> E) : ProbabilityMeasure E :=
  (isingTorusZeroFieldLaw (d := d) (k := k) beta).map
    (Measurable.of_discrete : Measurable X).aemeasurable


end
end StatMech.FrontierA
