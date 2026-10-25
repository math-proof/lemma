/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectCutClosedReducedEventWeight
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) : Real :=
  ∑ omega : FKRectCutClosedConfig R,
    A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) omega.1


def fkRectCutClosedReducedZ (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : FKRectCutClosedConfig R,
    fkRectCriticalReducedWeight R q omega.1

end
end StatMech.FrontierD
