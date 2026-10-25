/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedBoundaryCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FK

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]


def indexedOpenGraph (ends : E -> Sym2 V) (omega : E -> Bool) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | exists i, ends i = e /\ omega i = true}

end
end StatMech.FK
