/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeElitzur.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

section Elitzur

variable {Q E P : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P]

omit [DecidableEq P] in

theorem gaugePartition_pos (incidence : P -> Finset E) (K : P -> ℝ) :
    0 < gaugePartition incidence K := by
  unfold gaugePartition gaugeWeight
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


end Elitzur
end StatMech.FrontierA
