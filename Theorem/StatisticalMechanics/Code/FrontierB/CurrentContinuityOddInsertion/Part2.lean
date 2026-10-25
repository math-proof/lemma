/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFiniteSwitching
import Def.StatisticalMechanics.Code.FrontierB.CurrentContinuityOddInsertion.Part2


namespace StatMech.FrontierB

open Finset Sharpness

open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem summable_boundaryPairSummand
    (beta : Real) (interior internalSources exactSecondSources : Finset V)
    (P : Current V -> Prop) [DecidablePred P] :
    Summable (boundaryPairSummand G beta interior internalSources
      exactSecondSources P) := by
  have hbase := summable_mul_of_summable_norm
      (summable_norm_weight_ofEdgeFun G beta (fun _ => 1))
      (summable_norm_currentSum_summand G beta (fun _ => 1)
        exactSecondSources)
  have hprod : Summable (fun pq : EdgeCurrent G × EdgeCurrent G =>
      ‖weight G beta (fun _ => 1) (ofEdgeFun G pq.1)‖ *
        ‖(if sources G (ofEdgeFun G pq.2) = exactSecondSources then
          weight G beta (fun _ => 1) (ofEdgeFun G pq.2) else 0)‖) := by
    simpa only [norm_mul] using hbase.norm
  apply Summable.of_norm
  refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro pq
  by_cases hfirst : sources G (ofEdgeFun G pq.1) ∩ interior = internalSources <;>
    by_cases hsecond : sources G (ofEdgeFun G pq.2) = exactSecondSources <;>
    by_cases hP : P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) <;>
    simp [boundaryPairSummand, hfirst, hsecond, hP, norm_mul] <;> positivity

theorem tsum_boundaryPairSummand
    (beta : Real) (interior internalSources exactSecondSources : Finset V)
    (P : Current V -> Prop) [DecidablePred P] :
    ∑' pq, boundaryPairSummand G beta interior internalSources
        exactSecondSources P pq =
      boundarySourceGatedPairSum G beta (fun _ => 1) interior
        internalSources exactSecondSources P := by
  rw [boundarySourceGatedPairSum_eq_tsum]
  rfl


theorem beta_mul_boundarySource_notConnected_le_exteriorConnection
    (beta : Real) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset)
    (hleft : e.1.out.1 ∈ interior)
    (hright : e.1.out.2 ∈ interior) :
    beta * boundarySourceGatedPairSum G beta (fun _ => 1) interior
        {e.1.out.1, e.1.out.2} ∅
        (fun m => ¬ CurrentConnected G m
          e.1.out.1 e.1.out.2) ≤
      boundarySourceGatedPairSum G beta (fun _ => 1) interior ∅ ∅
        (fun m => ∃ z : V, z ∉ interior ∧
          CurrentConnected G m e.1.out.1 z) := by
  let u := e.1.out.1
  let v := e.1.out.2
  let U : Finset V := {u, v}
  let P : Current V -> Prop := fun m => ¬ CurrentConnected G m u v
  let Q : Current V -> Prop := fun m => ∃ z : V, z ∉ interior ∧
    CurrentConnected G m u z
  let enc : EdgeCurrent G × EdgeCurrent G -> EdgeCurrent G × EdgeCurrent G :=
    fun pq => (encodeCurrentEdgeOdd G e pq.1, pq.2)
  have henc : Function.Injective enc := by
    rintro ⟨m, n⟩ ⟨m', n'⟩ h
    have hm : encodeCurrentEdgeOdd G e m = encodeCurrentEdgeOdd G e m' :=
      congrArg Prod.fst h
    have hn : n = n' := congrArg Prod.snd h
    exact Prod.ext (encodeCurrentEdgeOdd_injective G e hm) hn
  let f : EdgeCurrent G × EdgeCurrent G -> Real := fun pq =>
    beta * boundaryPairSummand G beta interior U ∅ P pq
  let g : EdgeCurrent G × EdgeCurrent G -> Real := fun pq =>
    boundaryPairSummand G beta interior ∅ ∅ Q pq
  have hf : Summable f :=
    (summable_boundaryPairSummand G beta interior U ∅ P).mul_left beta
  have hg : Summable g :=
    summable_boundaryPairSummand G beta interior ∅ ∅ Q
  have hgNonneg : ∀ pq, 0 ≤ g pq := by
    rintro ⟨m, n⟩
    unfold g boundaryPairSummand
    split <;> split <;> split <;> simp_all
    exact mul_nonneg
      (Ising.acw_weight_nonneg G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) _)
      (Ising.acw_weight_nonneg G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) _)
  have hpoint : ∀ pq, f pq ≤ g (enc pq) := by
    rintro ⟨m, n⟩
    by_cases hsrc : sources G (ofEdgeFun G m) ∩ interior = U
    · by_cases hn : sources G (ofEdgeFun G n) = ∅
      · by_cases hnot : ¬ CurrentConnected G
            (ofEdgeFun G (fun a => m a + n a)) u v
        · have hsumZero : m e + n e = 0 := by
            by_contra hne
            have hpos : 0 < m e + n e := Nat.pos_of_ne_zero hne
            exact hnot (currentConnected_edgeEndpoints_of_pos G e
              (fun a => m a + n a) hpos)
          have hm : m e = 0 := Nat.eq_zero_of_add_eq_zero_right hsumZero
          have hUsub : U ⊆ interior := by
            intro x hx
            simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hleft
            · exact hright
          have hsrcEnc :
              sources G (ofEdgeFun G (encodeCurrentEdgeOdd G e m)) ∩ interior = ∅ := by
            rw [sources_encodeCurrentEdgeOdd_of_zero G e m hm]
            apply (sourceToggle_inter_eq_iff interior U
              (sources G (ofEdgeFun G m) ∆ U) hUsub).mp
            simpa only [symmDiff_symmDiff_cancel_right] using hsrc
          obtain ⟨z, hzout, huz⟩ :=
            boundarySource_notConnected_reaches_exterior G interior
              (by
                change e.1.out.1 ≠ e.1.out.2
                intro heq
                have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
                apply G.not_isDiag_of_mem_edgeSet hedge
                rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
                exact heq) m n hsrc hnot
          have huz' := currentConnected_add_right G
            (fun a => m a + n a) (currentUnitFlux G e) huz
          have hQ : Q (ofEdgeFun G (fun a =>
              encodeCurrentEdgeOdd G e m a + n a)) := by
            refine ⟨z, hzout, ?_⟩
            rw [encodeCurrentEdgeOdd_eq_add_unitFlux_of_zero G e m hm]
            simpa only [add_assoc, add_left_comm, add_comm] using huz'
          have hP : P (ofEdgeFun G (fun a => m a + n a)) := by
            exact hnot
          simp [f, g, enc, boundaryPairSummand, hsrc, hn, hnot,
            hsrcEnc, hP, hQ,
            weight_encodeCurrentEdgeOdd_of_zero G beta e m hm]
          simp only [mul_assoc]
          exact le_refl _
        · have hfzero : f (m, n) = 0 := by
            simp [f, boundaryPairSummand, hsrc, hn, P, hnot]
          rw [hfzero]
          exact hgNonneg _
      · simp [f, boundaryPairSummand, hsrc, hn, hgNonneg]
    · simp [f, boundaryPairSummand, hsrc, hgNonneg]
  have hsum := hf.tsum_le_tsum_of_inj enc henc
    (fun pq hp => hgNonneg pq) hpoint hg
  dsimp [f, g] at hsum
  rw [tsum_mul_left, tsum_boundaryPairSummand,
    tsum_boundaryPairSummand] at hsum
  simpa only [u, v, U, P, Q] using hsum


theorem beta_mul_boundarySource_twoPoint_gap_le_exteriorConnection_ratio
    (beta : Real) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset)
    (hleft : e.1.out.1 ∈ interior)
    (hright : e.1.out.2 ∈ interior) :
    beta *
        (boundarySourceCurrentSum G beta (fun _ => 1) interior
              {e.1.out.1, e.1.out.2} /
            boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ -
          currentSum G beta (fun _ => 1)
              {e.1.out.1, e.1.out.2} /
            currentSum G beta (fun _ => 1) ∅) ≤
      boundarySourceGatedPairSum G beta (fun _ => 1) interior ∅ ∅
          (fun m => ∃ z : V, z ∉ interior ∧
            CurrentConnected G m e.1.out.1 z) /
        (boundarySourceCurrentSum G beta (fun _ => 1) interior ∅ *
          currentSum G beta (fun _ => 1) ∅) := by
  let u := e.1.out.1
  let v := e.1.out.2
  let a := boundarySourceCurrentSum G beta (fun _ => 1) interior {u, v}
  let b := currentSum G beta (fun _ => 1) {u, v}
  let z := boundarySourceCurrentSum G beta (fun _ => 1) interior ∅
  let w := currentSum G beta (fun _ => 1) ∅
  let t := boundarySourceGatedPairSum G beta (fun _ => 1) interior ∅ ∅
    (fun m => ∃ y : V, y ∉ interior ∧ CurrentConnected G m u y)
  have hz : 0 < z := lt_of_lt_of_le Real.zero_lt_one
    (one_le_boundaryCurrentSum G beta (fun _ => 1) hbeta.le
      (fun _ => zero_le_one) interior)
  have hw : 0 < w := Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  have hgap : a * w - z * b =
      boundarySourceGatedPairSum G beta (fun _ => 1) interior {u, v} ∅
        (fun m => ¬ CurrentConnected G m u v) := by
    simpa only [a, b, z, w, u, v] using
      boundarySource_twoPoint_gap_eq_notConnected G beta (fun _ => 1)
        interior (by
          intro heq
          have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
          apply G.not_isDiag_of_mem_edgeSet hedge
          rw [← e.1.out_eq, Sym2.mk_isDiag_iff]
          exact heq) hleft hright
  have hins := beta_mul_boundarySource_notConnected_le_exteriorConnection
    G beta hbeta interior e hleft hright
  have hfrac : a / z - b / w = (a * w - z * b) / (z * w) := by
    field_simp [hz.ne', hw.ne']
  rw [hfrac, hgap]
  have hden : 0 < z * w := mul_pos hz hw
  change beta *
      (boundarySourceGatedPairSum G beta (fun _ => 1) interior {u, v} ∅
        (fun m => ¬ CurrentConnected G m u v) / (z * w)) ≤ t / (z * w)
  rw [← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hden).2 (by
    simpa only [t, u, v] using hins)

end StatMech.FrontierB
