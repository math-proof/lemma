/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part14
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_homogeneous_fullSource_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    (A : Finset V) (e0 : ↥G.edgeFinset)
    (m : ↥G.edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A)
    (hmpos : 0 < m e0) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A (∅ : Finset V) m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1) A (∅ : Finset V) := by
  let d := edgeCopySourcePairData_empty_of_fullSource G A m hfull
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_homogeneous_data
      G hβpos A (∅ : Finset V) e0 d (by simpa [d] using hmpos)

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_homogeneous_currentSource_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    (A : Finset V) (e0 : ↥G.edgeFinset)
    (m : ↥G.edgeFinset → ℕ)
    (hsrc : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A)
    (hmpos : 0 < m e0) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A (∅ : Finset V) m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1) A (∅ : Finset V) := by
  have hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A := by
    rw [Sharpness.FluxEdgeCopy.sources_eq,
      Sharpness.FluxEdgeCopy.profileFlux_univ]
    exact hsrc
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_homogeneous_fullSource_empty
      G hβpos A e0 m hfull hmpos

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in


theorem walkDeg_odd_iff_walk
    {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    {a b : V} (p : H.Walk a b) (x : V) :
    Odd (Sharpness.walkDeg p x) ↔ (x = a ∨ x = b) ∧ a ≠ b := by
  revert x
  induction p with
  | nil =>
      intro x
      simp only [Sharpness.walkDeg_nil]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro ⟨_, hne⟩
        exact absurd rfl hne
  | @cons a v b h p ih =>
      intro x
      rw [Sharpness.walkDeg_cons]
      by_cases hxa : x = a
      · subst x
        have hav : a ≠ v := h.ne
        have hodd_a : Odd (Sharpness.walkDeg p a) ↔ a = b := by
          rw [ih a]
          constructor
          · rintro ⟨hor, _⟩
            rcases hor with hav_eq | hab
            · exact absurd hav_eq hav
            · exact hab
          · intro hab
            refine ⟨Or.inr hab, ?_⟩
            intro hvb
            exact hav (hab.trans hvb.symm)
        have ha_mem : a ∈ (s(a, v) : Sym2 V) := by
          simp [Sym2.mem_iff]
        rw [if_pos ha_mem, add_comm, Nat.odd_add_one, hodd_a]
        constructor
        · intro hab
          exact ⟨Or.inl rfl, hab⟩
        · intro htarget
          exact htarget.2
      · by_cases hxv : x = v
        · subst x
          have hodd_v : Odd (Sharpness.walkDeg p v) ↔ v ≠ b := by
            rw [ih v]
            constructor
            · intro hodd
              exact hodd.2
            · intro hvb
              exact ⟨Or.inl rfl, hvb⟩
          have hv_mem : v ∈ (s(a, v) : Sym2 V) := by
            simp [Sym2.mem_iff]
          rw [if_pos hv_mem, add_comm, Nat.odd_add_one, hodd_v]
          constructor
          · intro hnot
            have hvb : v = b := not_not.mp hnot
            refine ⟨Or.inr hvb, ?_⟩
            intro hab
            exact h.ne (hab.trans hvb.symm)
          · rintro ⟨hor, _⟩
            rcases hor with hva | hvb
            · exact absurd hva hxa
            · exact fun hvb_ne => hvb_ne hvb
        · have hx_not_mem : x ∉ (s(a, v) : Sym2 V) := by
            simpa [Sym2.mem_iff] using not_or.mpr ⟨hxa, hxv⟩
          rw [if_neg hx_not_mem, zero_add, ih x]
          constructor
          · rintro ⟨hor, hvb⟩
            rcases hor with hxv_eq | hxb
            · exact absurd hxv_eq hxv
            · refine ⟨Or.inr hxb, ?_⟩
              intro hab
              exact hxa (hxb.trans hab.symm)
          · rintro ⟨hor, _hab⟩
            rcases hor with hxa_eq | hxb
            · exact absurd hxa_eq hxa
            · refine ⟨Or.inr hxb, ?_⟩
              intro hvb
              exact hxv (hxb.trans hvb.symm)

set_option linter.style.longLine false in


theorem sources_ofEdgeFun_walk_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (p : G.Walk a b) (hab : a ≠ b) :
    let m : ↥G.edgeFinset → ℕ := fun e => p.edges.count e.1
    Sharpness.sources G (Sharpness.ofEdgeFun G m) = ({a, b} : Finset V) := by
  classical
  dsimp
  ext x
  rw [Sharpness.mem_sources]
  have hsub : ∀ e ∈ p.edges, e ∈ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.Walk.edges_subset_edgeSet p he)
  have hflux :
      Sharpness.incidentFlux G
          (Sharpness.ofEdgeFun G
            (fun e : ↥G.edgeFinset => p.edges.count e.1)) x =
        Sharpness.walkDeg p x := by
    unfold Sharpness.incidentFlux Sharpness.ofEdgeFun
    calc
      ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e),
          (if h : e ∈ G.edgeFinset then
            p.edges.count ((⟨e, h⟩ : ↥G.edgeFinset).1) else 0) =
          ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e),
            p.edges.count e := by
        refine Finset.sum_congr rfl ?_
        intro e he
        have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
        rw [dif_pos heG]
      _ = Sharpness.walkDeg p x :=
        Sharpness.sum_count_eq_walkDeg G p x hsub
  rw [hflux]
  rw [walkDeg_odd_iff_walk p x]
  constructor
  · rintro ⟨hx, _⟩
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx
  · intro hx
    exact ⟨by simpa [Finset.mem_insert, Finset.mem_singleton] using hx, hab⟩

set_option linter.style.longLine false in


theorem expectationJ_pair_pos_of_walk_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    {a b : V} (p : G.Walk a b) (hab : a ≠ b) :
    0 < Sharpness.expectationJ G β (fun _ => 1)
      ({a, b} : Finset V) := by
  let m : ↥G.edgeFinset → ℕ := fun e => p.edges.count e.1
  have hsrc :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({a, b} : Finset V) := by
    simpa [m] using sources_ofEdgeFun_walk_count G p hab
  have hweight :
      0 < Sharpness.weight G β (fun _ => 1)
        (Sharpness.ofEdgeFun G m) :=
    weight_ofEdgeFun_pos_of_pos_on_support G β (fun _ => 1)
      hβpos m (by intro e _he; norm_num)
  exact
    expectationJ_pos_of_positive_edgeCurrent G β (fun _ => 1)
      ({a, b} : Finset V) hβpos.le (by intro e; norm_num)
      m hsrc hweight

set_option linter.style.longLine false in


theorem expectationJ_pair_pos_of_boxGraph_reachable
    {d n : ℕ} {β : ℝ} (hβpos : 0 < β)
    {a b : FK.boxVerts d n} (hab : a ≠ b) :
    0 < Sharpness.expectationJ (FK.boxGraph d n) β (fun _ => 1)
      ({a, b} : Finset (FK.boxVerts d n)) := by
  rcases boxGraph_reachable d n a b with ⟨walk⟩
  exact
    expectationJ_pair_pos_of_walk_count (FK.boxGraph d n) hβpos walk hab

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointExpectationJ_pos_of_endpoint_ne
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    0 < Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v) := by
  rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
  exact
    expectationJ_pair_pos_of_boxGraph_reachable
      (d := 3) (n := 2 * n) hβpos hov

set_option linter.style.longLine false in


theorem doubledBoxInnerPairExpectationJ_pos_of_endpoint_ne
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    0 < Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxInnerPairSource n v w) :=
  expectationJ_pair_pos_of_boxGraph_reachable
    (d := 3) (n := 2 * n) hβpos hvw

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_pos_of_endpoint_ne
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n}
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    0 < doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum] using
    sourcePairSum_empty_pos_of_expectationJ_pos
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (doubledBoxOriginToInnerEndpointExpectationJ_pos_of_endpoint_ne
        (β := β) hβpos (n := n) (v := v) hov)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointInnerPairSourcePairSum_pos_of_endpoints_ne
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    0 <
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) :=
  sourcePairSum_pos_of_expectationJ_pos
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
    (doubledBoxOriginToInnerEndpointSource n w)
    (doubledBoxInnerPairSource n v w)
    (doubledBoxOriginToInnerEndpointExpectationJ_pos_of_endpoint_ne
      (β := β) hβpos (n := n) (v := w) how)
    (doubledBoxInnerPairExpectationJ_pos_of_endpoint_ne
      (β := β) hβpos (n := n) (v := v) (w := w) hvw)

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_pathCount_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    {a b : V} (p : G.Path a b) (hab : a ≠ b)
    (e0 : ↥G.edgeFinset)
    (he0 : 0 < p.1.edges.count e0.1) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1)
            ({a, b} : Finset V) (∅ : Finset V) m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1)
          ({a, b} : Finset V) (∅ : Finset V) := by
  let m : ↥G.edgeFinset → ℕ := fun e => p.1.edges.count e.1
  have hsrc :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({a, b} : Finset V) := by
    simpa [m] using sources_ofEdgeFun_path_count G p hab
  have hmpos : 0 < m e0 := by
    simpa [m] using he0
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_homogeneous_currentSource_empty
      G hβpos ({a, b} : Finset V) e0 m hsrc hmpos

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_pathCount_eq_zero_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    {a b : V} (p : G.Path a b) (hab : a ≠ b)
    (e0 : ↥G.edgeFinset)
    (hbound :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1)
            ({a, b} : Finset V) (∅ : Finset V) m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1)
          ({a, b} : Finset V) (∅ : Finset V)) :
    p.1.edges.count e0.1 = 0 := by
  by_contra hne
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_pathCount_empty
      G hβpos p hab e0 (Nat.pos_of_ne_zero hne) hbound

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_walkCount_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    {a b : V} (p : G.Walk a b) (hab : a ≠ b)
    (e0 : ↥G.edgeFinset)
    (he0 : 0 < p.edges.count e0.1) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1)
            ({a, b} : Finset V) (∅ : Finset V) m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1)
          ({a, b} : Finset V) (∅ : Finset V) := by
  let m : ↥G.edgeFinset → ℕ := fun e => p.edges.count e.1
  have hsrc :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({a, b} : Finset V) := by
    simpa [m] using sources_ofEdgeFun_walk_count G p hab
  have hmpos : 0 < m e0 := by
    simpa [m] using he0
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_homogeneous_currentSource_empty
      G hβpos ({a, b} : Finset V) e0 m hsrc hmpos

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_walkCount_eq_zero_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    {a b : V} (p : G.Walk a b) (hab : a ≠ b)
    (e0 : ↥G.edgeFinset)
    (hbound :
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1)
            ({a, b} : Finset V) (∅ : Finset V) m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1)
          ({a, b} : Finset V) (∅ : Finset V)) :
    p.edges.count e0.1 = 0 := by
  by_contra hne
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_walkCount_empty
      G hβpos p hab e0 (Nat.pos_of_ne_zero hne) hbound

set_option linter.style.longLine false in


theorem walkThroughEdge_count_pos
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a u v b : V}
    (pLeft : G.Walk a u) (huv : G.Adj u v) (pRight : G.Walk v b) :
    0 <
      (pLeft.append (SimpleGraph.Walk.cons huv pRight)).edges.count
        (s(u, v) : Sym2 V) := by
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons]
  exact List.count_pos_iff.mpr
    (List.mem_append.mpr (Or.inr (by simp)))

set_option linter.style.longLine false in

theorem walkThroughEdge_count_pos_of_edge_eq
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj]
    {a u v b : V}
    (pLeft : G.Walk a u) (huv : G.Adj u v) (pRight : G.Walk v b)
    (e0 : ↥G.edgeFinset) (hedge : e0.1 = s(u, v)) :
    0 <
      (pLeft.append (SimpleGraph.Walk.cons huv pRight)).edges.count
        e0.1 := by
  rw [hedge]
  exact walkThroughEdge_count_pos pLeft huv pRight

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_walkThroughEdge_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβpos : 0 < β)
    {a b u v : V}
    (pLeft : G.Walk a u) (huv : G.Adj u v) (pRight : G.Walk v b)
    (hab : a ≠ b)
    (e0 : ↥G.edgeFinset) (hedge : e0.1 = s(u, v)) :
    ¬
      (∑' m : ↥G.edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1)
            ({a, b} : Finset V) (∅ : Finset V) m)) ≤
        edgeCopySourcePairSum G β (fun _ => 1)
          ({a, b} : Finset V) (∅ : Finset V) := by
  let p : G.Walk a b := pLeft.append (SimpleGraph.Walk.cons huv pRight)
  have he0 : 0 < p.edges.count e0.1 := by
    simpa [p] using
      walkThroughEdge_count_pos_of_edge_eq pLeft huv pRight e0 hedge
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_not_of_walkCount_empty
      G hβpos p hab e0 he0

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_eq_same_beta_of_support_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset)
    (hsupport :
      ∀ m : ↥G.edgeFinset → ℕ,
        m e0 ≠ 0 → edgeCopySourcePairSummand G β J A B m = 0) :
    (∑' m : ↥G.edgeFinset → ℕ,
      (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)) =
      edgeCopySourcePairSum G β J A B := by
  have hsum :
      edgeCopySourcePairSum G β J A B =
        ∑' m : ↥G.edgeFinset → ℕ,
          edgeCopySourcePairSummand G β J A B m := by
    simp [edgeCopySourcePairSum, edgeCopySourcePairSummand]
  rw [hsum]
  refine tsum_congr (fun m => ?_)
  by_cases hm : m e0 = 0
  · rw [hm]
    norm_num
  · rw [hsupport m hm]
    ring

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_of_support_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (e0 : ↥G.edgeFinset)
    (hsupport :
      ∀ m : ↥G.edgeFinset → ℕ,
        m e0 ≠ 0 → edgeCopySourcePairSummand G β J A B m = 0) :
    (∑' m : ↥G.edgeFinset → ℕ,
      (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)) ≤
      edgeCopySourcePairSum G β J A B := by
  rw [edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_eq_same_beta_of_support_zero
    G β J A B e0 hsupport]

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_iff_support_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (e0 : ↥G.edgeFinset) :
    ((∑' m : ↥G.edgeFinset → ℕ,
      (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β J A B m)) ≤
      edgeCopySourcePairSum G β J A B) ↔
      ∀ m : ↥G.edgeFinset → ℕ,
        edgeCopySourcePairSummand G β J A B m ≠ 0 → m e0 = 0 := by
  constructor
  · intro hle m hsummand_ne
    exact
      edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_eq_zero_of_summand_ne_zero
        G hβ J hJ A B e0 hle m hsummand_ne
  · intro hsupport
    exact
      edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_of_support_zero
        G β J A B e0
        (fun m hmne => by
          by_contra hsummand_ne
          exact hmne (hsupport m hsummand_ne))

theorem beta_pow_le_two_beta_pow {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    β ^ k ≤ (2 * β) ^ k := by
  exact pow_le_pow_left₀ hβ (by linarith : β ≤ 2 * β) k

theorem natSucc_mul_beta_pow_div_factorial_le_two_beta_pow_div_factorial
    {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    (((k + 1 : ℕ) : ℝ) * (β ^ k / (Nat.factorial k : ℝ))) ≤
      (2 * β) ^ k / (Nat.factorial k : ℝ) := by
  have hcast : (((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k) := by
    exact_mod_cast nat_succ_le_two_pow k
  have hpow : 0 ≤ β ^ k := pow_nonneg hβ k
  have hnum :
      (((k + 1 : ℕ) : ℝ) * β ^ k) ≤ (2 : ℝ) ^ k * β ^ k :=
    mul_le_mul_of_nonneg_right hcast hpow
  have hfac : 0 ≤ (Nat.factorial k : ℝ) := by positivity
  calc
    (((k + 1 : ℕ) : ℝ) * (β ^ k / (Nat.factorial k : ℝ)))
        = (((k + 1 : ℕ) : ℝ) * β ^ k) /
            (Nat.factorial k : ℝ) := by ring
    _ ≤ ((2 : ℝ) ^ k * β ^ k) / (Nat.factorial k : ℝ) :=
      div_le_div_of_nonneg_right hnum hfac
    _ = (2 * β) ^ k / (Nat.factorial k : ℝ) := by rw [mul_pow]

theorem beta_pow_div_factorial_le_two_beta_pow_div_factorial
    {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    β ^ k / (Nat.factorial k : ℝ) ≤
      (2 * β) ^ k / (Nat.factorial k : ℝ) := by
  exact div_le_div_of_nonneg_right
    (beta_pow_le_two_beta_pow hβ k) (by positivity)

set_option linter.style.longLine false in


theorem two_pow_sum_multiplicity_mul_weight_ofEdgeFun_eq_two_beta_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (m : ↥G.edgeFinset → ℕ) :
    (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) *
      Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m) =
      Sharpness.weight G (2 * β) (fun _ => 1)
        (Sharpness.ofEdgeFun G m) := by
  classical
  rw [Sharpness.weight_ofEdgeFun, Sharpness.weight_ofEdgeFun]
  simp only [mul_one]
  rw [← Finset.prod_pow_eq_pow_sum
    (s := (Finset.univ : Finset ↥G.edgeFinset))
    (f := m) (a := (2 : ℝ))]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro e _he
  rw [mul_pow]
  ring

set_option linter.style.longLine false in


theorem two_pow_sum_multiplicity_mul_edgeCopySourcePairSummand_eq_two_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (A B : Finset V) (m : ↥G.edgeFinset → ℕ) :
    (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) *
      edgeCopySourcePairSummand G β (fun _ => 1) A B m =
      edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m := by
  rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight,
    edgeCopySourcePairSummand_eq_witness_card_mul_weight]
  let cardR : ℝ := ((edgeCopySourcePairWitnesses G A B m).card : ℝ)
  let wβ := Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)
  let w2 := Sharpness.weight G (2 * β) (fun _ => 1)
    (Sharpness.ofEdgeFun G m)
  change (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) * (cardR * wβ) =
    cardR * w2
  have hw :
      (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) * wβ = w2 := by
    simpa [wβ, w2] using
      two_pow_sum_multiplicity_mul_weight_ofEdgeFun_eq_two_beta_weight
        G β m
  calc
    (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) * (cardR * wβ) =
        cardR * ((2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) * wβ) := by
      ring
    _ = cardR * w2 := by rw [hw]

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_mul_weight_le_two_beta_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) :
    ((edgeCopySourceSector G A m).card : ℝ) *
      Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m) ≤
      Sharpness.weight G (2 * β) (fun _ => 1)
        (Sharpness.ofEdgeFun G m) := by
  have hcard :=
    edgeCopySourceSector_card_cast_le_two_pow_sum_multiplicity G A m
  have hweight :
      0 ≤ Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m) :=
    weight_ofEdgeFun_nonneg_of_nonneg G β (fun _ => 1) hβ
      (by intro e; norm_num) m
  calc
    ((edgeCopySourceSector G A m).card : ℝ) *
        Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m) ≤
        (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) *
          Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m) := by
      exact mul_le_mul_of_nonneg_right hcard hweight
    _ = Sharpness.weight G (2 * β) (fun _ => 1)
          (Sharpness.ofEdgeFun G m) :=
      two_pow_sum_multiplicity_mul_weight_ofEdgeFun_eq_two_beta_weight
        G β m

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_mul_weight_update_succ_le_two_beta_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    ((edgeCopySourceSector G A
      (Function.update m e0 (m e0 + 1))).card : ℝ) *
      Sharpness.weight G β (fun _ => 1)
        (Sharpness.ofEdgeFun G
          (Function.update m e0 (m e0 + 1))) ≤
      Sharpness.weight G (2 * β) (fun _ => 1)
        (Sharpness.ofEdgeFun G
          (Function.update m e0 (m e0 + 1))) := by
  exact
    edgeCopySourceSector_card_mul_weight_le_two_beta_weight
      G hβ A (Function.update m e0 (m e0 + 1))

set_option linter.style.longLine false in


theorem edgeCopySourceSector_sum_sourcePairSummand_le_two_beta_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) :
    (∑ B : Finset V,
      edgeCopySourcePairSummand G β (fun _ => 1) A B m) ≤
      Sharpness.weight G (2 * β) (fun _ => 1)
        (Sharpness.ofEdgeFun G m) := by
  rw [← edgeCopySourceSector_card_mul_weight_eq_sum_sourcePairSummand
    G β (fun _ => 1) A m]
  exact edgeCopySourceSector_card_mul_weight_le_two_beta_weight G hβ A m

set_option linter.style.longLine false in


theorem edgeCopySourceSector_sum_sourcePairSummand_update_succ_le_two_beta_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (∑ B : Finset V,
      edgeCopySourcePairSummand G β (fun _ => 1) A B
        (Function.update m e0 (m e0 + 1))) ≤
      Sharpness.weight G (2 * β) (fun _ => 1)
        (Sharpness.ofEdgeFun G
          (Function.update m e0 (m e0 + 1))) := by
  exact
    edgeCopySourceSector_sum_sourcePairSummand_le_two_beta_weight
      G hβ A (Function.update m e0 (m e0 + 1))

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_update_succ_mul_edgeCopySourcePairSummand_le_two_mul_two_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (S A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    ((edgeCopySourceSector G S
      (Function.update m e0 (m e0 + 1))).card : ℝ) *
      edgeCopySourcePairSummand G β (fun _ => 1) A B m ≤
      2 * edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m := by
  have hcard :=
    edgeCopySourceSector_card_cast_update_succ_le_two_pow_sum_multiplicity_add_one
      G S m e0
  have hsummand_nonneg :
      0 ≤ edgeCopySourcePairSummand G β (fun _ => 1) A B m :=
    edgeCopySourcePairSummand_nonneg G β (fun _ => 1) A B m hβ
      (by intro e; norm_num)
  calc
    ((edgeCopySourceSector G S
        (Function.update m e0 (m e0 + 1))).card : ℝ) *
        edgeCopySourcePairSummand G β (fun _ => 1) A B m ≤
        (2 : ℝ) ^ ((∑ e : ↥G.edgeFinset, m e) + 1) *
          edgeCopySourcePairSummand G β (fun _ => 1) A B m := by
      exact mul_le_mul_of_nonneg_right hcard hsummand_nonneg
    _ = 2 * edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m := by
      rw [pow_succ]
      calc
        (2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) * 2 *
            edgeCopySourcePairSummand G β (fun _ => 1) A B m =
            2 * ((2 : ℝ) ^ (∑ e : ↥G.edgeFinset, m e) *
              edgeCopySourcePairSummand G β (fun _ => 1) A B m) := by
          ring
        _ = 2 * edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m := by
          rw [two_pow_sum_multiplicity_mul_edgeCopySourcePairSummand_eq_two_beta]

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_weight_ofEdgeFun_le_two_beta_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (((m e0 + 1 : ℕ) : ℝ) *
      Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)) ≤
      Sharpness.weight G (2 * β) (fun _ => 1)
        (Sharpness.ofEdgeFun G m) := by
  classical
  rw [Sharpness.weight_ofEdgeFun, Sharpness.weight_ofEdgeFun]
  simp only [mul_one]
  let a : ↥G.edgeFinset → ℝ :=
    fun e => β ^ (m e) / (Nat.factorial (m e) : ℝ)
  let b : ↥G.edgeFinset → ℝ :=
    fun e => (2 * β) ^ (m e) / (Nat.factorial (m e) : ℝ)
  change (((m e0 + 1 : ℕ) : ℝ) * ∏ e : ↥G.edgeFinset, a e) ≤
    ∏ e : ↥G.edgeFinset, b e
  have ha_nonneg : ∀ e, 0 ≤ a e := by
    intro e
    exact div_nonneg (pow_nonneg hβ _) (by positivity)
  have hb_nonneg : ∀ e, 0 ≤ b e := by
    intro e
    exact div_nonneg (pow_nonneg (mul_nonneg (by norm_num) hβ) _)
      (by positivity)
  have hpoint : ∀ e, a e ≤ b e := by
    intro e
    exact beta_pow_div_factorial_le_two_beta_pow_div_factorial hβ (m e)
  have hpoint_e0 :
      (((m e0 + 1 : ℕ) : ℝ) * a e0) ≤ b e0 := by
    exact
      natSucc_mul_beta_pow_div_factorial_le_two_beta_pow_div_factorial
        hβ (m e0)
  have hprod_rest :
      (∏ e ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, a e) ≤
        ∏ e ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, b e := by
    exact Finset.prod_le_prod
      (fun e _ => ha_nonneg e)
      (fun e _ => hpoint e)
  have hrest_nonneg :
      0 ≤ ∏ e ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, a e := by
    exact Finset.prod_nonneg fun e _ => ha_nonneg e
  have hprod_a :
      (∏ e : ↥G.edgeFinset, a e) =
        a e0 *
          ∏ e ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, a e := by
    rw [Finset.mul_prod_erase
      (s := (Finset.univ : Finset ↥G.edgeFinset))
      (f := a) (a := e0) (Finset.mem_univ e0)]
  have hprod_b :
      (∏ e : ↥G.edgeFinset, b e) =
        b e0 *
          ∏ e ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, b e := by
    rw [Finset.mul_prod_erase
      (s := (Finset.univ : Finset ↥G.edgeFinset))
      (f := b) (a := e0) (Finset.mem_univ e0)]
  calc
    (((m e0 + 1 : ℕ) : ℝ) * ∏ e : ↥G.edgeFinset, a e)
        = (((m e0 + 1 : ℕ) : ℝ) * a e0) *
            ∏ e ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, a e := by
          rw [hprod_a]
          ring
    _ ≤ b e0 *
          ∏ e ∈ (Finset.univ : Finset ↥G.edgeFinset).erase e0, b e :=
        mul_le_mul hpoint_e0 hprod_rest hrest_nonneg (hb_nonneg e0)
    _ = ∏ e : ↥G.edgeFinset, b e := by
          rw [hprod_b]

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (((m e0 + 1 : ℕ) : ℝ) *
      edgeCopySourcePairSummand G β (fun _ => 1) A B m) ≤
      edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m := by
  rw [edgeCopySourcePairSummand_eq_witness_card_mul_weight,
    edgeCopySourcePairSummand_eq_witness_card_mul_weight]
  let cardR : ℝ := ((edgeCopySourcePairWitnesses G A B m).card : ℝ)
  let wβ := Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)
  let w2 := Sharpness.weight G (2 * β) (fun _ => 1)
    (Sharpness.ofEdgeFun G m)
  change (((m e0 + 1 : ℕ) : ℝ) * (cardR * wβ)) ≤ cardR * w2
  have hw : (((m e0 + 1 : ℕ) : ℝ) * wβ) ≤ w2 :=
    edgeMultiplicitySucc_mul_weight_ofEdgeFun_le_two_beta_weight G hβ m e0
  have hcard : 0 ≤ cardR := by
    dsimp [cardR]
    positivity
  calc
    (((m e0 + 1 : ℕ) : ℝ) * (cardR * wβ))
        = cardR * ((((m e0 + 1 : ℕ) : ℝ) * wβ) : ℝ) := by ring
    _ ≤ cardR * w2 := mul_le_mul_of_nonneg_left hw hcard

set_option linter.style.longLine false in


theorem edgeCopySourceSector_card_update_succ_mul_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_mul_four_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (S A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    ((edgeCopySourceSector G S
      (Function.update m e0 (m e0 + 1))).card : ℝ) *
      (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β (fun _ => 1) A B m) ≤
      2 * edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m := by
  have hsector :
      ((edgeCopySourceSector G S
        (Function.update m e0 (m e0 + 1))).card : ℝ) *
        edgeCopySourcePairSummand G β (fun _ => 1) A B m ≤
        2 * edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m :=
    edgeCopySourceSector_card_update_succ_mul_edgeCopySourcePairSummand_le_two_mul_two_beta
      G hβ S A B m e0
  have hcoord :
      (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m) ≤
        edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m :=
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_beta
      G (mul_nonneg (by norm_num) hβ) A B m e0
  calc
    ((edgeCopySourceSector G S
        (Function.update m e0 (m e0 + 1))).card : ℝ) *
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A B m) =
        ((m e0 + 1 : ℕ) : ℝ) *
          (((edgeCopySourceSector G S
            (Function.update m e0 (m e0 + 1))).card : ℝ) *
            edgeCopySourcePairSummand G β (fun _ => 1) A B m) := by
      ring
    _ ≤ ((m e0 + 1 : ℕ) : ℝ) *
          (2 * edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m) := by
      exact mul_le_mul_of_nonneg_left hsector (by positivity)
    _ = 2 * (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m) := by
      ring
    _ ≤ 2 * edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m := by
      exact mul_le_mul_of_nonneg_left hcoord (by norm_num)

set_option linter.style.longLine false in


theorem edgeMultiplicity_mul_edgeCopySourcePairSummand_le_two_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) (e0 : ↥G.edgeFinset) :
    (((m e0 : ℕ) : ℝ) *
      edgeCopySourcePairSummand G β (fun _ => 1) A B m) ≤
      edgeCopySourcePairSummand G (2 * β) (fun _ => 1) A B m := by
  have hcoef :
      (((m e0 : ℕ) : ℝ) : ℝ) ≤ (((m e0 + 1 : ℕ) : ℝ) : ℝ) := by
    exact_mod_cast Nat.le_succ (m e0)
  have hsummand_nonneg :
      0 ≤ edgeCopySourcePairSummand G β (fun _ => 1) A B m :=
    edgeCopySourcePairSummand_nonneg G β (fun _ => 1) A B m hβ
      (by intro e; norm_num)
  exact
    (mul_le_mul_of_nonneg_right hcoef hsummand_nonneg).trans
      (edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_beta
        G hβ A B m e0)

set_option linter.style.longLine false in


theorem edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_two_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β : ℝ} (hβ : 0 ≤ β) (A B : Finset V)
    (e0 : ↥G.edgeFinset) :
    (∑' m : ↥G.edgeFinset → ℕ,
      (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β (fun _ => 1) A B m)) ≤
      edgeCopySourcePairSum G (2 * β) (fun _ => 1) A B := by
  rw [edgeCopySourcePairSum]
  exact
    (summable_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand
      G β (fun _ => 1) A B e0).tsum_le_tsum
      (fun m =>
        edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_beta
          G hβ A B m e0)
      (edgeCopySourcePairSummand_summable G (2 * β) (fun _ => 1) A B)


theorem edgeCopySourcePairEmptyCollapsedTerm_eq_zero_of_not_fullSource
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) ≠ A) :
    edgeCopySourcePairEmptyCollapsedTerm G β J A m = 0 := by
  rw [edgeCopySourcePairEmptyCollapsedTerm_eq_multiplicity_mul_weight]
  rw [edgeCopySourcePairEmptyCollapsedMultiplicity_eq_zero_of_not_fullSource
    G A m hsrc]
  simp


end Exact3D
end StatMech
