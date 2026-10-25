/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section LocalGauge

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


omit [Fintype E] [Fintype P] [DecidableEq P] in
@[simp] theorem localGaugeTransform_apply (star : Q -> Finset E) (v : Q)
    (omega : GaugeConfig E) (e : E) :
    localGaugeTransform star v omega e =
      if e ∈ star v then !(omega e) else omega e := rfl

omit [Fintype E] [Fintype P] [DecidableEq P] in

@[simp] theorem localGaugeTransform_involutive (star : Q -> Finset E) (v : Q)
    (omega : GaugeConfig E) :
    localGaugeTransform star v (localGaugeTransform star v omega) = omega := by
  funext e
  by_cases he : e ∈ star v <;> simp [localGaugeTransform, he]

end LocalGauge
end StatMech.FrontierA
