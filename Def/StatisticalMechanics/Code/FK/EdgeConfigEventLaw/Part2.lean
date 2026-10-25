/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigEventLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw
open scoped BigOperators
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ecz_eventWeight (p q : Real) (A : Set (ecz_ClosedOff G)) : Real :=
  ∑ omega : ecz_ClosedOff G,
    A.indicator (fun omega => fkWeight G p q omega.1) omega


end
end StatMech.FK
