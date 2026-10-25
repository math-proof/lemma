/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part3
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def cycleCompleteWitnessVertex [Nonempty V]
    (hG : G.Preconnected) (q : CycleCompleteConstraint G) : V :=
  Classical.choose (exists_odd_closed_walk G hG q)

noncomputable def cycleCompleteWitnessWalk [Nonempty V]
    (hG : G.Preconnected) (q : CycleCompleteConstraint G) :
    G.Walk (cycleCompleteWitnessVertex G hG q)
      (cycleCompleteWitnessVertex G hG q) :=
  Classical.choose (Classical.choose_spec (exists_odd_closed_walk G hG q))

end
end StatMech.FrontierA
