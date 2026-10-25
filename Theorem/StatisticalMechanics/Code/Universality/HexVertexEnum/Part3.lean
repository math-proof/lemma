/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part2


namespace StatMech.Universality

open Complex

open HexWalk


theorem combinedSummand_at_p {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ} (hend : (ofTurns a h0 ts).EndsAt (v + du)) :
    combinedSummand region a h0 v du ts
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts := by
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega * du) _ _ ts
        (fun hq => hexMid_p_ne_q hdu (hend.symm.trans hq)),
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega ^ 2 * du) _ _ ts
        (fun hr => hexMid_p_ne_r hdu (hend.symm.trans hr))]
  ring


theorem combinedSummand_at_q {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ} (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega * du)) :
    combinedSummand region a h0 v du ts
      = ((v + hexOmega * du) - v)
          * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts := by
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + du) _ _ ts
        (fun hp => hexMid_p_ne_q hdu (hp.symm.trans hend)),
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega ^ 2 * du) _ _ ts
        (fun hr => hexMid_q_ne_r hdu (hend.symm.trans hr))]
  ring


theorem combinedSummand_at_r {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ} (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du)) :
    combinedSummand region a h0 v du ts
      = ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts := by
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + du) _ _ ts
        (fun hp => hexMid_p_ne_r hdu (hp.symm.trans hend)),
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega * du) _ _ ts
        (fun hq => hexMid_q_ne_r hdu (hq.symm.trans hend))]
  ring


theorem vertexSum_eq_tsum_combinedSummand (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = ∑' ts, combinedSummand region a h0 v du ts := by
  unfold parafObservable combinedSummand
  rw [← hp.tsum_mul_left, ← hq.tsum_mul_left, ← hr.tsum_mul_left]
  rw [← (hp.mul_left _).tsum_add (hq.mul_left _), ← ((hp.mul_left _).add (hq.mul_left _)).tsum_add (hr.mul_left _)]


end StatMech.Universality
