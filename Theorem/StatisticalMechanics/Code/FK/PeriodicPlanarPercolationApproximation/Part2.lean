/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V]

@[simp] theorem PeriodicGraph.bufferedRoot_val (P : PeriodicGraph V) (n : Nat) :
    (P.bufferedRoot n : V) = P.root := rfl


end StatMech.FK.PeriodicPlanar
