/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete
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


def walkOddSupport : {x y : V} -> G.Walk x y -> Finset (Sym2 V)
  | _, _, .nil => ∅
  | _, _, .cons (u := u) (v := v) _ p =>
      gaugeToggle s(u, v) (walkOddSupport p)

end
end StatMech.FrontierA
