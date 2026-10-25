/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone.Part3
import Theorem.StatisticalMechanics.Code.FK.DlrInfiniteSandwich
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.FK.FreeDLRKernel
open MeasureTheory Set SimpleGraph Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin]
  [Fintype Vout] [DecidableEq Vout]


noncomputable def freeNestedWiringPMF
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : PMF (SimpleGraph Vin) :=
  PMF.ofFintype
    (fun C => ENNReal.ofReal (freeNestedWiringWeight Gout ιV p q C)) <| by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun C _ => freeNestedWiringWeight_nonneg Gout ιV hp hp1 hq C),
        freeNestedWiringWeight_sum_eq_one Gout ιV hι hp hp1 hq]
      norm_num


noncomputable def freeNestedWiringMeasure
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (SimpleGraph Vin) :=
  ⟨(freeNestedWiringPMF Gout ιV hι hp hp1 hq).toMeasure, inferInstance⟩


end FK
end StatMech
