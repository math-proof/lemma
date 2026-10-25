/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeElitzur.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeElitzur
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section Elitzur

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

noncomputable def gaugeWilsonExpectation (incidence : P -> Finset E)
    (K : P -> ℝ) (L : Finset E) : ℝ :=
  gaugeWilsonNumerator incidence K L / gaugePartition incidence K


def IsLocallyGaugeCharged (star : Q -> Finset E) (L : Finset E) : Prop :=
  ∃ v, Odd (L ∩ star v).card

end Elitzur
end StatMech.FrontierA
