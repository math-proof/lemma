/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeHighTemp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeHighTemp
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section GaugeHypergraph

variable {E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

abbrev GaugeConfig (E : Type*) := E -> Bool


end GaugeHypergraph
end StatMech.FrontierA
