/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneResidualLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalEventMass_pos_of_mem
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) (omega : R.Configuration) (homega : omega ∈ A) :
    0 < fkRectCriticalEventMass R q A := by
  unfold fkRectCriticalEventMass
  apply Finset.sum_pos'
  · intro eta heta
    exact Set.indicator_nonneg
      (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _
  · refine ⟨omega, Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem homega]
    unfold fkRectCriticalRandomClusterProb
    exact div_pos (fkRectCriticalReducedWeight_pos R hq omega)
      (fkRectCriticalReducedZ_pos R hq)


theorem fkRectRightBand_distinguished_reachable
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut <= x.val) :
    (fkRectInducedGraph R
      (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable
        (fkRectRightBandRowOne R cut x hx)
        (fkRectRightBandLastRow R cut x hx) := by
  have hheight : 2 < R.height := R.height_gt_two
  have hxlt : x.val < R.width := x.isLt
  let v (n : Nat) (hn1 : 1 <= n) (hnH : n < R.height) :
      FKRectRightStripBandVertex R cut 1 (R.height - 1) :=
    ⟨(x, ⟨n, hnH⟩), by
      change cut <= x.val ∧ 1 <= n ∧ n <= R.height - 1
      omega⟩
  have hreach : forall n (hn1 : 1 <= n) (hnH : n < R.height),
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable
          (v 1 le_rfl (by omega)) (v n hn1 hnH) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        intro hn1 hnH
        by_cases hn0 : n = 0
        · subst n
          exact SimpleGraph.Reachable.refl _
        · have hn1' : 1 <= n := by omega
          have hnH' : n < R.height := by omega
          have hprev := ih hn1' hnH'
          have hpred : SixVertexArrows.cyclicPred R.height_pos
              (⟨n + 1, hnH⟩ : Fin R.height) =
              (⟨n, hnH'⟩ : Fin R.height) := by
            apply Fin.ext
            rw [fkRectCyclicPred_val]
            simp only [if_neg (by omega : n + 1 ≠ 0)]
            omega
          have hadj : (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1))).Adj
              (v n hn1' hnH') (v (n + 1) hn1 hnH) := by
            change (fkRectTorusGraph R).Adj
              (x, (⟨n, hnH'⟩ : Fin R.height))
              (x, (⟨n + 1, hnH⟩ : Fin R.height))
            simpa [hpred] using
              (fkRectTorusGraph_adj_verticalPred R x
                (⟨n + 1, hnH⟩ : Fin R.height)).symm
          exact hprev.trans hadj.reachable
  have hlast := hreach (R.height - 1) (by omega) (by omega)
  have hstart : v 1 le_rfl (by omega) =
      fkRectRightBandRowOne R cut x hx := by
    apply Subtype.ext
    rfl
  have hend : v (R.height - 1) (by omega) (by omega) =
      fkRectRightBandLastRow R cut x hx := by
    apply Subtype.ext
    rfl
  rwa [hstart, hend] at hlast


theorem fkRectRightBandConnectionProduct_pos
    (R : FKRectTorus) (cut : Nat) {q : Real} (hq : 0 < q)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hreaches : ∀ xy ∈ t,
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable xy.1 xy.2) :
    0 < ∏ xy ∈ t,
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2 := by
  apply Finset.prod_pos
  intro xy hxy
  exact FK.twoPointFun_pos_of_reachable
    (fkRectInducedGraph R
      (fkRectRightStripBand R cut 1 (R.height - 1)))
    (fkRectCriticalP_pos hq) (fkRectCriticalP_lt_one hq) hq
    (hreaches xy hxy)


theorem fkRectCriticalWindingOneMass_pos_of_source
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 <= q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t)
    (hproduct : 0 < ∏ xy ∈ t,
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2)
    (hbarrier : 0 < fkRectCriticalEventMass R q
      (fkRectSourceLeftBarrier R leftRight gap)) :
    0 < fkRectCriticalWindingOneMass R q := by
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq
  have hlower :=
    fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans
      R leftRight cut hsep hleft hq hgap x hx hchosen t hspans
  unfold fkRectCriticalWindingOneMass
  exact (mul_pos (mul_pos hc hproduct) hbarrier).trans_le hlower


theorem windingOne_negLogRate_le_source_cost
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    (hleft : leftRight + 1 < R.width)
    {q : Real} (hq : 1 <= q)
    {gap : R.EdgeIndex} (hgap : gap ∈ fkRectHorizontalCutEdges R)
    (x : Fin R.width) (hx : cut <= x.val)
    (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hspans : FKRectRightBandConnectionChainSpans R cut x hx t)
    (hproduct : 0 < ∏ xy ∈ t,
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut 1 (R.height - 1)))
        (fkRectCriticalP q) q xy.1 xy.2)
    (hbarrier : 0 < fkRectCriticalEventMass R q
      (fkRectSourceLeftBarrier R leftRight gap)) :
    -Real.log (fkRectCriticalWindingOneMass R q) / R.height <=
      -Real.log (∏ xy ∈ t,
          FK.twoPointFun
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut 1 (R.height - 1)))
            (fkRectCriticalP q) q xy.1 xy.2) / R.height +
        -Real.log (fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap)) / R.height +
        -Real.log (FK.cFE (fkRectCriticalP q) q) / R.height := by
  let P : Real := ∏ xy ∈ t,
    FK.twoPointFun
      (fkRectInducedGraph R
        (fkRectRightStripBand R cut 1 (R.height - 1)))
      (fkRectCriticalP q) q xy.1 xy.2
  let B : Real := fkRectCriticalEventMass R q
    (fkRectSourceLeftBarrier R leftRight gap)
  let c : Real := FK.cFE (fkRectCriticalP q) q
  have hc : 0 < c := by
    dsimp [c]
    exact FK.cFE_pos
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
      (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq
  have hmass : 0 < fkRectCriticalWindingOneMass R q :=
    fkRectCriticalWindingOneMass_pos_of_source R leftRight cut hsep hleft
      hq hgap x hx hchosen t hspans hproduct hbarrier
  have hlower : c * P * B <= fkRectCriticalWindingOneMass R q := by
    simpa [c, P, B, fkRectCriticalWindingOneMass] using
      (fkRectSource_barrierConnectionProduct_le_windingOneMass_of_spans
        R leftRight cut hsep hleft hq hgap x hx hchosen t hspans)
  have hlog := Real.log_le_log (mul_pos (mul_pos hc hproduct) hbarrier) hlower
  rw [Real.log_mul (mul_pos hc hproduct).ne' hbarrier.ne',
    Real.log_mul hc.ne' hproduct.ne'] at hlog
  have hnum : -Real.log (fkRectCriticalWindingOneMass R q) <=
      -Real.log P + -Real.log B + -Real.log c := by
    linarith
  have hh : 0 <= (R.height : Real) := by positivity
  calc
    -Real.log (fkRectCriticalWindingOneMass R q) / R.height <=
        (-Real.log P + -Real.log B + -Real.log c) / R.height :=
      div_le_div_of_nonneg_right hnum hh
    _ = -Real.log P / R.height + -Real.log B / R.height +
        -Real.log c / R.height := by ring
    _ = _ := by rfl


end
end StatMech.FrontierD
