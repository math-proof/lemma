/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section LocalGauge

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]


def HasEvenPlaquetteStarIncidence (incidence : P -> Finset E)
    (star : Q -> Finset E) : Prop :=
  ∀ v p, Even (incidence p ∩ star v).card

end LocalGauge
end StatMech.FrontierA
