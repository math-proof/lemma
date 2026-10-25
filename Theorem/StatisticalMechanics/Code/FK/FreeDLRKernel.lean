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
import Def.StatisticalMechanics.Code.FK.FreeDLRKernel
open MeasureTheory Set SimpleGraph Filter Topology
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin]
  [Fintype Vout] [DecidableEq Vout]


theorem freeNestedWiringWeight_nonneg
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (C : SimpleGraph Vin) :
    0 ≤ freeNestedWiringWeight Gout ιV p q C := by
  classical
  unfold freeNestedWiringWeight
  exact Finset.sum_nonneg fun ψ _ => by
    split
    · exact Finset.sum_nonneg fun σ _ => fkProb_nonneg Gout hp hp1 hq σ
    · exact le_rfl


theorem freeNestedWiringWeight_sum_eq_one
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ C : SimpleGraph Vin, freeNestedWiringWeight Gout ιV p q C = 1 := by
  classical
  rw [show (∑ C : SimpleGraph Vin, freeNestedWiringWeight Gout ιV p q C) =
      ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        ∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          fkProb Gout p q σ by
    unfold freeNestedWiringWeight
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ψ _
    simp]
  have hsum := ocd_sum_fibreMass_eq_one
    (Gout := Gout) (bdryOut := bdp_noBdry (Vout := Vout)) hι hp hp1 hq
  simpa only [bdp_bcProb_noBdry_eq_fkProb] using hsum


end FK
end StatMech
