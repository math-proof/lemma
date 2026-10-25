/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Def.StatisticalMechanics.Code.FrontierB.CurrentTraceInsertion
open MeasureTheory
open scoped ENNReal BigOperators symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem zeroCurrentEdge_apply_same (e : G.edgeFinset) (m : EdgeCurrent G) :
    zeroCurrentEdge G e m e = 0 := by
  simp [zeroCurrentEdge]

@[simp] theorem zeroCurrentEdge_apply_of_ne (e f : G.edgeFinset)
    (hfe : f ≠ e) (m : EdgeCurrent G) :
    zeroCurrentEdge G e m f = m f := by
  simp [zeroCurrentEdge, hfe]

@[simp] theorem forceCurrentEdgePositive_apply_same
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m e = if m e = 0 then 2 else m e := by
  by_cases h : m e = 0 <;> simp [forceCurrentEdgePositive, h]

@[simp] theorem forceCurrentEdgePositive_apply_of_ne
    (e f : G.edgeFinset) (hfe : f ≠ e) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m f = m f := by
  by_cases h : m e = 0 <;> simp [forceCurrentEdgePositive, h, hfe]

theorem forceCurrentEdgePositive_eq_self_iff
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m = m ↔ m e ≠ 0 := by
  constructor
  · intro h hm0
    have he := congrFun h e
    simp [forceCurrentEdgePositive, hm0] at he
  · intro h
    simp [forceCurrentEdgePositive, h]

theorem forceCurrentEdgePositive_ne_zero
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e m e ≠ 0 := by
  by_cases h : m e = 0 <;> simp [forceCurrentEdgePositive, h]

theorem forceCurrentEdgePositive_zeroCurrentEdge
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    forceCurrentEdgePositive G e (zeroCurrentEdge G e m) =
      Function.update m e 2 := by
  funext f
  by_cases hfe : f = e
  · subst f
    simp [forceCurrentEdgePositive]
  · simp [forceCurrentEdgePositive, zeroCurrentEdge, hfe]

theorem forceCurrentEdgePositive_preimage_iff_of_eq_two
    (e : G.edgeFinset) (m a : EdgeCurrent G) (hm : m e = 2) :
    forceCurrentEdgePositive G e a = m <->
      a = m \/ a = zeroCurrentEdge G e m := by
  constructor
  · intro h
    by_cases ha : a e = 0
    · right
      funext f
      by_cases hfe : f = e
      · subst f
        simp [zeroCurrentEdge, ha]
      · have hf := congrFun h f
        simpa [forceCurrentEdgePositive, ha, zeroCurrentEdge, hfe] using hf
    · left
      simpa [forceCurrentEdgePositive, ha] using h
  · rintro (rfl | rfl)
    · simp [forceCurrentEdgePositive, hm]
    · rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm]
      · simp [hfe]

theorem forceCurrentEdgePositive_preimage_iff_of_ne_two
    (e : G.edgeFinset) (m a : EdgeCurrent G) (hm0 : m e ≠ 0)
    (hm2 : m e ≠ 2) :
    forceCurrentEdgePositive G e a = m ↔ a = m := by
  constructor
  · intro h
    by_cases ha : a e = 0
    · have he := congrFun h e
      simp [forceCurrentEdgePositive, ha] at he
      exact (hm2 he.symm).elim
    · simpa [forceCurrentEdgePositive, ha] using h
  · rintro rfl
    simp [forceCurrentEdgePositive, hm0]

theorem forceCurrentEdgePositive_no_preimage_of_eq_zero
    (e : G.edgeFinset) (m a : EdgeCurrent G) (hm : m e = 0) :
    forceCurrentEdgePositive G e a ≠ m := by
  intro h
  exact forceCurrentEdgePositive_ne_zero G e a
    (by simpa [hm] using congrFun h e)

theorem sources_twoFluxAt (e : G.edgeFinset) :
    sources G (ofEdgeFun G (twoFluxAt G e)) = ∅ := by
  ext v
  simp only [mem_sources]
  apply iff_of_false
  · rw [Nat.not_odd_iff_even]
    unfold incidentFlux
    by_cases hv : v ∈ e.1
    · have hefilter : e.1 ∈ G.edgeFinset.filter (fun f => v ∈ f) := by
        exact Finset.mem_filter.mpr ⟨e.2, hv⟩
      rw [← Finset.sum_erase_add _ _ hefilter]
      have hrest : ∑ f ∈ (G.edgeFinset.filter (fun f => v ∈ f)).erase e.1,
          ofEdgeFun G (twoFluxAt G e) f = 0 := by
        apply Finset.sum_eq_zero
        intro f hf
        have hfne : f ≠ e.1 := Finset.ne_of_mem_erase hf
        have hfG : f ∈ G.edgeFinset :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase hf)).1
        simp [ofEdgeFun, twoFluxAt, hfG, Subtype.ext_iff, hfne]
      rw [hrest]
      simp [ofEdgeFun, twoFluxAt, e.2]
    · have hzero : ∑ f ∈ G.edgeFinset.filter (fun f => v ∈ f),
          ofEdgeFun G (twoFluxAt G e) f = 0 := by
        apply Finset.sum_eq_zero
        intro f hf
        have hffilter := Finset.mem_filter.mp hf
        have hfne : f ≠ e.1 := by
          intro h
          apply hv
          simpa [h] using hffilter.2
        simp [ofEdgeFun, twoFluxAt, hffilter.1, Subtype.ext_iff, hfne]
      rw [hzero]
      exact Even.zero
  · simp

theorem forceCurrentEdgePositive_eq_add_twoFluxAt_of_zero
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    forceCurrentEdgePositive G e m = fun f => m f + twoFluxAt G e f := by
  funext f
  by_cases hfe : f = e
  · subst f
    simp [forceCurrentEdgePositive, twoFluxAt, hm]
  · simp [forceCurrentEdgePositive, twoFluxAt, hm, hfe]


theorem sources_forceCurrentEdgePositive
    (e : G.edgeFinset) (m : EdgeCurrent G) :
    sources G (ofEdgeFun G (forceCurrentEdgePositive G e m)) =
      sources G (ofEdgeFun G m) := by
  by_cases hm : m e = 0
  · rw [forceCurrentEdgePositive_eq_add_twoFluxAt_of_zero G e m hm,
      ← ofEdgeFun_add, sources_add, sources_twoFluxAt]
    simp
  · simp [forceCurrentEdgePositive, hm]


theorem weight_forceCurrentEdgePositive_of_zero
    (beta : ℝ) (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    weight G beta (fun _ => 1)
        (ofEdgeFun G (forceCurrentEdgePositive G e m)) =
      weight G beta (fun _ => 1) (ofEdgeFun G m) * (beta ^ 2 / 2) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  have hforce : forceCurrentEdgePositive G e m = Function.update m e 2 := by
    simp [forceCurrentEdgePositive, hm]
  rw [hforce]
  simp only [mul_one]
  let term : G.edgeFinset → ℕ → ℝ := fun f k => beta ^ k / Nat.factorial k
  change (∏ f ∈ Finset.univ, term f (Function.update m e 2 f)) =
    (∏ f ∈ Finset.univ, term f (m f)) * (beta ^ 2 / 2)
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
  have hcomp :
      (∏ f ∈ (Finset.univ : Finset G.edgeFinset) \ {e},
          term f (Function.update m e 2 f)) =
        ∏ f ∈ (Finset.univ : Finset G.edgeFinset) \ {e}, term f (m f) := by
    apply Finset.prod_congr rfl
    intro f hf
    have hfe : f ≠ e := by
      have hnot := (Finset.mem_sdiff.mp hf).2
      simpa using hnot
    simp [hfe]
  rw [hcomp]
  simp only [term, hm, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  simp
  ring


theorem currentPMF_forceCurrentEdgePositive_apply_of_zero
    (beta : ℝ) (hbeta : 0 < beta) (A : Finset V)
    (hA : 0 < currentSum G beta (fun _ => 1) A)
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA
        (forceCurrentEdgePositive G e m) =
      ENNReal.ofReal (beta ^ 2 / 2) *
        currentPMF G beta (fun _ => 1) hbeta.le (fun _ => zero_le_one) A hA m := by
  rw [currentPMF_apply, currentPMF_apply]
  unfold currentRawMass
  rw [sources_forceCurrentEdgePositive]
  by_cases hsrc : sources G (ofEdgeFun G m) = A
  · simp only [hsrc, if_true]
    rw [weight_forceCurrentEdgePositive_of_zero G beta e m hm,
      ENNReal.ofReal_mul]
    · ring
    · exact Ising.acw_weight_nonneg G beta (fun _ => 1)
        hbeta.le (fun _ => zero_le_one) _
  · simp [hsrc]


theorem boundaryCurrentPMF_forceCurrentEdgePositive_apply_of_zero
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
        (fun _ => zero_le_one) interior (forceCurrentEdgePositive G e m) =
      ENNReal.ofReal (beta ^ 2 / 2) *
        boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
          (fun _ => zero_le_one) interior m := by
  rw [boundaryCurrentPMF_apply, boundaryCurrentPMF_apply]
  unfold boundaryCurrentRawMass
  rw [sources_forceCurrentEdgePositive]
  by_cases hsrc : sources G (ofEdgeFun G m) ∩ interior = ∅
  · simp only [hsrc, if_true]
    rw [weight_forceCurrentEdgePositive_of_zero G beta e m hm,
      ENNReal.ofReal_mul]
    · ring
    · exact Ising.acw_weight_nonneg G beta (fun _ => 1)
        hbeta.le (fun _ => zero_le_one) _
  · simp [hsrc]

set_option maxHeartbeats 3000000 in

theorem PMF.map_forceCurrentEdgePositive_apply_of_eq_two
    (p : PMF (EdgeCurrent G)) (e : G.edgeFinset) (m : EdgeCurrent G)
    (hm : m e = 2) :
    PMF.map (forceCurrentEdgePositive G e) p m =
      p m + p (zeroCurrentEdge G e m) := by
  letI : DecidableEq (EdgeCurrent G) := Classical.decEq _
  rw [PMF.map_apply, ENNReal.tsum_eq_add_tsum_ite m]
  have hmpos : m e ≠ 0 := by omega
  have hself : forceCurrentEdgePositive G e m = m :=
    (forceCurrentEdgePositive_eq_self_iff G e m).2 hmpos
  rw [if_pos hself.symm]
  congr 1
  let z := zeroCurrentEdge G e m
  have hzeroNe : z ≠ m := by
      intro h
      have he := congrFun h e
      simp [z, zeroCurrentEdge, hm] at he
  have hforce : forceCurrentEdgePositive G e z = m := by
      rw [forceCurrentEdgePositive_zeroCurrentEdge]
      funext f
      by_cases hfe : f = e
      · subst f
        simp [hm]
      · simp [hfe]
  rw [← show (if z = m then 0 else
      if m = forceCurrentEdgePositive G e z then p z else 0) = p z by
    simp [hzeroNe, hforce]]
  apply tsum_eq_single z
  intro a hane
  by_cases ham : a = m
  · subst a
    simp
  · have hnot : forceCurrentEdgePositive G e a ≠ m := by
      intro hforce'
      rcases (forceCurrentEdgePositive_preimage_iff_of_eq_two G e m a hm).1 hforce' with
        h | h
      · exact ham h
      · exact hane h
    simp [ham, hnot.symm]

set_option maxHeartbeats 800000 in

theorem PMF.map_forceCurrentEdgePositive_apply_of_ne_two
    (p : PMF (EdgeCurrent G)) (e : G.edgeFinset) (m : EdgeCurrent G)
    (hm0 : m e ≠ 0) (hm2 : m e ≠ 2) :
    PMF.map (forceCurrentEdgePositive G e) p m = p m := by
  letI : DecidableEq (EdgeCurrent G) := Classical.decEq _
  rw [PMF.map_apply]
  have hself : forceCurrentEdgePositive G e m = m :=
    (forceCurrentEdgePositive_eq_self_iff G e m).2 hm0
  have hfm : (if m = forceCurrentEdgePositive G e m then p m else 0) = p m := by
    simp [hself]
  rw [← hfm]
  apply tsum_eq_single m
  intro a hane
  have hnot : forceCurrentEdgePositive G e a ≠ m := by
    intro hforce
    exact hane ((forceCurrentEdgePositive_preimage_iff_of_ne_two
      G e m a hm0 hm2).1 hforce)
  simp [hnot.symm]

set_option maxHeartbeats 800000 in

theorem PMF.map_forceCurrentEdgePositive_apply_of_eq_zero
    (p : PMF (EdgeCurrent G)) (e : G.edgeFinset) (m : EdgeCurrent G)
    (hm : m e = 0) :
    PMF.map (forceCurrentEdgePositive G e) p m = 0 := by
  letI : DecidableEq (EdgeCurrent G) := Classical.decEq _
  rw [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro a
  rw [if_neg]
  exact (forceCurrentEdgePositive_no_preimage_of_eq_zero G e m a hm).symm


end StatMech.FrontierB
