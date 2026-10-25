/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part6
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]


def indexedBcEventMass (ends : E -> Sym2 V)
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (p q : Real) (A : Set (E -> Bool)) : Real :=
  ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    indexedBcProb ends C p q omega

end
end StatMech.FK
