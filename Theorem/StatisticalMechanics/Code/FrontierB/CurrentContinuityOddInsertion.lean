/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFiniteSwitching
import Def.StatisticalMechanics.Code.FrontierB.CurrentContinuityOddInsertion


namespace StatMech.FrontierB

open Finset Sharpness

open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem encodeCurrentEdgeOdd_injective (e : G.edgeFinset) :
    Function.Injective (encodeCurrentEdgeOdd G e) := by
  intro m n hmn
  funext f
  by_cases hfe : f = e
  · subst f
    have heq := congrFun hmn e
    simp only [encodeCurrentEdgeOdd, if_pos] at heq
    by_cases hm : m e = 0 <;> by_cases hn : n e = 0
    · simpa [hm, hn]
    · simp [hm, hn] at heq
    · simp [hm, hn] at heq
    · simp [hm, hn] at heq
      omega
  · have heq := congrFun hmn f
    simpa [encodeCurrentEdgeOdd, hfe] using heq

theorem encodeCurrentEdgeOdd_eq_add_unitFlux_of_zero
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    encodeCurrentEdgeOdd G e m = fun f => m f + currentUnitFlux G e f := by
  funext f
  by_cases hfe : f = e
  · subst f
    simp [encodeCurrentEdgeOdd, currentUnitFlux, hm]
  · simp [encodeCurrentEdgeOdd, currentUnitFlux, hfe]


theorem sources_currentUnitFlux (e : G.edgeFinset) :
    sources G (ofEdgeFun G (currentUnitFlux G e)) =
      {e.1.out.1, e.1.out.2} := by
  ext v
  rw [mem_sources]
  have hcurrent :
      ofEdgeFun G (currentUnitFlux G e) = fun f => if f = e.1 then 1 else 0 := by
    funext f
    unfold ofEdgeFun currentUnitFlux
    split
    · rename_i hf
      by_cases hfe : f = e.1
      · subst f
        simp
      · have hsub : (⟨f, hf⟩ : G.edgeFinset) ≠ e := by
          intro h
          exact hfe (congrArg Subtype.val h)
        simp [hfe, hsub]
    · rename_i hf
      have hfe : f ≠ e.1 := by
        intro h
        subst f
        exact hf e.2
      simp [hfe]
  rw [hcurrent]
  have hflux :
      incidentFlux G (fun f => if f = e.1 then 1 else 0) v =
        if v ∈ e.1 then 1 else 0 := by
    unfold incidentFlux
    by_cases hv : v ∈ e.1
    · rw [if_pos hv]
      simp [hv, e.2]
    · rw [if_neg hv]
      apply Finset.sum_eq_zero
      intro f hf
      have hfe : f ≠ e.1 := by
        intro h
        subst f
        exact hv (Finset.mem_filter.mp hf).2
      simp [hfe]
  rw [hflux]
  have hviff : v ∈ e.1 ↔ v = e.1.out.1 ∨ v = e.1.out.2 := by
    calc
      v ∈ e.1 ↔ v ∈ s(e.1.out.1, e.1.out.2) :=
        iff_of_eq (congrArg (fun z : Sym2 V => v ∈ z) e.1.out_eq).symm
      _ ↔ v = e.1.out.1 ∨ v = e.1.out.2 := Sym2.mem_iff
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases hv : v ∈ e.1
  · rw [if_pos hv]
    exact ⟨fun _ => hviff.mp hv, fun _ => odd_one⟩
  · rw [if_neg hv]
    exact ⟨fun hodd => (by simp at hodd), fun hends => (hv (hviff.mpr hends)).elim⟩


theorem sources_encodeCurrentEdgeOdd_of_zero
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    sources G (ofEdgeFun G (encodeCurrentEdgeOdd G e m)) =
      sources G (ofEdgeFun G m) ∆
        {e.1.out.1, e.1.out.2} := by
  rw [encodeCurrentEdgeOdd_eq_add_unitFlux_of_zero G e m hm,
    ← ofEdgeFun_add, sources_add, sources_currentUnitFlux]


theorem weight_encodeCurrentEdgeOdd_of_zero
    (beta : Real) (e : G.edgeFinset) (m : EdgeCurrent G) (hm : m e = 0) :
    weight G beta (fun _ => 1)
        (ofEdgeFun G (encodeCurrentEdgeOdd G e m)) =
      beta * weight G beta (fun _ => 1) (ofEdgeFun G m) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  simp only [mul_one]
  let term : G.edgeFinset -> Nat -> Real :=
    fun _ k => beta ^ k / Nat.factorial k
  change (∏ f ∈ Finset.univ, term f (encodeCurrentEdgeOdd G e m f)) =
    beta * ∏ f ∈ Finset.univ, term f (m f)
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ e)]
  have hcomp :
      (∏ f ∈ (Finset.univ : Finset G.edgeFinset) \ {e},
          term f (encodeCurrentEdgeOdd G e m f)) =
        ∏ f ∈ (Finset.univ : Finset G.edgeFinset) \ {e}, term f (m f) := by
    apply Finset.prod_congr rfl
    intro f hf
    have hfe : f ≠ e := by
      have hnot := (Finset.mem_sdiff.mp hf).2
      simpa using hnot
    simp [encodeCurrentEdgeOdd, hfe]
  rw [hcomp]
  simp [term, encodeCurrentEdgeOdd, hm]


theorem currentConnected_edgeEndpoints_of_pos
    (e : G.edgeFinset) (m : EdgeCurrent G) (hm : 0 < m e) :
    CurrentConnected G (ofEdgeFun G m)
      e.1.out.1 e.1.out.2 := by
  apply SimpleGraph.Adj.reachable
  have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
  constructor
  · change G.Adj e.1.out.1 e.1.out.2
    have hedge : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
    rw [← SimpleGraph.mem_edgeSet]
    rw [hout]
    exact hedge
  · change 1 ≤ ofEdgeFun G m s(e.1.out.1, e.1.out.2)
    rw [hout]
    simp [ofEdgeFun, e.2]
    omega

end StatMech.FrontierB
