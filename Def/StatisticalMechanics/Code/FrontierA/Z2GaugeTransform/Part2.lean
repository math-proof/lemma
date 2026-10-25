/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section LocalGauge

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


omit [Fintype E] [Fintype P] [DecidableEq P] in

def localGaugeEquiv (star : Q -> Finset E) (v : Q) :
    GaugeConfig E ≃ GaugeConfig E where
  toFun := localGaugeTransform star v
  invFun := localGaugeTransform star v
  left_inv := localGaugeTransform_involutive star v
  right_inv := localGaugeTransform_involutive star v

end LocalGauge
end StatMech.FrontierA
