/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part13


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem endpointParafObservable_start_eq_one_of_unique
    (R : HexFiniteRegion) (h0 : ℤ)
    (hunique : ∀ ts : List ℤ,
      (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt R.start →
        ts = []) :
    endpointParafObservable R.inRegion R.start h0 R.start
      (5 / 8) hexChi = 1 := by
  unfold endpointParafObservable
  calc
    (∑' ts : List ℤ,
        endpointParafSummand R.inRegion R.start h0 R.start
          (5 / 8) hexChi ts) =
        endpointParafSummand R.inRegion R.start h0 R.start
          (5 / 8) hexChi [] := by
      apply tsum_eq_single
      intro ts hts
      by_cases hguard :
          (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
            (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
            (ofTurns R.start h0 ts).EndsAt R.start
      · exact (hts (hunique ts hguard)).elim
      · unfold endpointParafSummand
        rw [if_neg hguard]
    _ = 1 := endpointParafSummand_nil R.inRegion R.start h0
      (5 / 8) hexChi R.start_mem

end
end StatMech.Universality
