/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section LocalGauge

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


omit [Fintype E] [Fintype P] [DecidableEq P] in


theorem wilsonSpin_localGaugeTransform_eq (star : Q -> Finset E)
    (L : Finset E) (hclosed : IsGaugeClosed star L)
    (v : Q) (omega : GaugeConfig E) :
    wilsonSpin L (localGaugeTransform star v omega) = wilsonSpin L omega := by
  rw [wilsonSpin_localGaugeTransform]
  rw [(hclosed v).neg_one_pow]
  simp

end LocalGauge
end StatMech.FrontierA
