/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part8
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem thinTranslationClosureCounterexampleConfig_horizontal
    (x y : ZMod 8) :
    thinTranslationClosureCounterexampleConfig
        (torusHorizontalEdge 8 x y) = false := by
  have hcode : (torusEdgeCodeEquiv 8).symm
      (torusHorizontalEdge 8 x y) =
        ((x, y), TorusEdgeOrientation.horizontal) := by
    apply (torusEdgeCodeEquiv 8).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  rw [thinTranslationClosureCounterexampleConfig, hcode]

@[simp] theorem thinTranslationClosureCounterexampleConfig_vertical
    (x y : ZMod 8) :
    thinTranslationClosureCounterexampleConfig
        (torusVerticalEdge 8 x y) =
      decide (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4)) := by
  have hcode : (torusEdgeCodeEquiv 8).symm
      (torusVerticalEdge 8 x y) =
        ((x, y), TorusEdgeOrientation.vertical) := by
    apply (torusEdgeCodeEquiv 8).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  rw [thinTranslationClosureCounterexampleConfig, hcode]


theorem thinTranslationClosureCounterexample_translated_open
    (y : ℤ) (hy0 : 0 ≤ y) (hy3 : y ≤ 3) :
    IsOpenEdge 2
      (torusPlanarPullback 8
        (torusAmbientTranslateConfig 8 ![0, 1]
          thinTranslationClosureCounterexampleConfig))
      ![0, y] ![0, y + 1] := by
  rw [torusPlanarPullback_translate]
  refine ⟨sw_adj_vertSucc 0 y, ?_⟩
  change torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
    (Sym2.map (fun x => x + ![0, 1]) s(![0, y], ![0, y + 1])) = true
  rw [Sym2.map_mk]
  have hopen : torusPlanarPullback 8
      thinTranslationClosureCounterexampleConfig
        s(![0, y + 1], ![0, (y + 1) + 1]) = true := by
    rw [torusPlanarPullback_vertical,
      thinTranslationClosureCounterexampleConfig_vertical,
      decide_eq_true_eq]
    constructor
    · norm_num
    · interval_cases y <;> norm_num
  simpa using hopen


theorem thinTranslationClosureCounterexample_translated_crossing :
    VerticalCrossing
      (torusPlanarPullback 8
        (torusAmbientTranslateConfig 8 ![0, 1]
          thinTranslationClosureCounterexampleConfig))
      0 2 0 4 := by
  let omega := torusPlanarPullback 8
    (torusAmbientTranslateConfig 8 ![0, 1]
      thinTranslationClosureCounterexampleConfig)
  let v0 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 0], by simp [mem_rect]⟩
  let v1 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 1], by simp [mem_rect]⟩
  let v2 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 2], by simp [mem_rect]⟩
  let v3 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 3], by simp [mem_rect]⟩
  let v4 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 4], by simp [mem_rect]⟩
  have h01 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v0 v1 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v0, v1] using
      (thinTranslationClosureCounterexample_translated_open 0
        (by norm_num) (by norm_num)).2
  have h12 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v1 v2 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v1, v2] using
      (thinTranslationClosureCounterexample_translated_open 1
        (by norm_num) (by norm_num)).2
  have h23 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v2 v3 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v2, v3] using
      (thinTranslationClosureCounterexample_translated_open 2
        (by norm_num) (by norm_num)).2
  have h34 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v3 v4 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v3, v4] using
      (thinTranslationClosureCounterexample_translated_open 3
        (by norm_num) (by norm_num)).2
  refine ⟨⟨![0, 0], by simp [bottomSide, mem_rect]⟩,
    ⟨![0, 4], by simp [topSide, mem_rect]⟩, ?_⟩
  have hconn : ConnectedWithin 2 omega (rect 0 2 0 4) v0 v4 :=
    h01.reachable.trans (h12.reachable.trans
      (h23.reachable.trans h34.reachable))
  simpa [omega, v0, v4] using hconn


theorem thinTranslationClosureCounterexample_mem_closure :
    bdcTorusThinCrossingTranslationClosure 8 2 1
      thinTranslationClosureCounterexampleConfig := by
  refine ⟨![0, 1], ?_⟩
  refine ⟨bdcLongRectangleOriginIndex 2 (by norm_num), ?_⟩
  simpa [bdcLongRectangleXOffset, bdcLongRectangleYOffset,
    bdcLongRectangleOriginIndex] using
    thinTranslationClosureCounterexample_translated_crossing


theorem thinTranslationClosureCounterexample_vertical_iff (x y : ℤ) :
    torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, y], ![x, y + 1]) = true ↔
      (x : ZMod 8) = 0 ∧
        ((y : ZMod 8) = 1 ∨ (y : ZMod 8) = 2 ∨
          (y : ZMod 8) = 3 ∨ (y : ZMod 8) = 4) := by
  rw [torusPlanarPullback_vertical,
    thinTranslationClosureCounterexampleConfig_vertical,
    decide_eq_true_eq]


theorem thinTranslationClosureCounterexample_cut_step
    {a c h : ℤ} {p q : Site 2}
    (hp : p ∈ rect a (a + 2) c (c + 4))
    (hq : q ∈ rect a (a + 2) c (c + 4))
    (hadj : (hypercubicLattice 2).Adj p q)
    (hopen : torusPlanarPullback 8
      thinTranslationClosureCounterexampleConfig s(p, q) = true)
    (hple : p 1 ≤ h)
    (hclosed : ∀ x : ℤ,
      torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, h], ![x, h + 1]) ≠ true) :
    q 1 ≤ h := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  rw [mem_rect] at hp hq
  by_contra hqle
  push Not at hqle
  have hp1 : p 1 = h := by omega
  have hq1 : q 1 = h + 1 := by omega
  have hpq0 : p 0 = q 0 := by omega
  have hpe : p = ![p 0, h] := by
    funext i
    fin_cases i <;> simp [hp1]
  have hqe : q = ![p 0, h + 1] := by
    funext i
    fin_cases i <;> simp [hpq0.symm, hq1]
  apply hclosed (p 0)
  rw [hpe, hqe] at hopen
  simpa using hopen


theorem thinTranslationClosureCounterexample_cut_walk
    {a c h : ℤ}
    (hclosed : ∀ x : ℤ,
      torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, h], ![x, h + 1]) ≠ true)
    {p q : (rect a (a + 2) c (c + 4) : Set (Site 2))}
    (w : (openSubgraphInduce 2
      (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig)
      (rect a (a + 2) c (c + 4))).Walk p q)
    (hp : (p : Site 2) 1 ≤ h) :
    (q : Site 2) 1 ≤ h := by
  induction w with
  | nil => exact hp
  | @cons u v z huv _ ih =>
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact ih (thinTranslationClosureCounterexample_cut_step
        u.2 v.2 huv.1 huv.2 hp hclosed)


theorem thinTranslationClosureCounterexample_no_vertical_of_cut
    {a c h : ℤ} (hch : c ≤ h) (hhc : h < c + 4)
    (hclosed : ∀ x : ℤ,
      torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, h], ![x, h + 1]) ≠ true) :
    ¬ VerticalCrossing
      (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig)
      a (a + 2) c (c + 4) := by
  rintro ⟨p, q, hpq⟩
  have hp1 : (p : Site 2) 1 = c := p.2.2
  have hq1 : (q : Site 2) 1 = c + 4 := q.2.2
  have hbound := thinTranslationClosureCounterexample_cut_walk hclosed hpq.some
    (by rw [hp1]; exact hch)
  rw [hq1] at hbound
  omega


theorem thinTranslationClosureCounterexample_cut_zero (x : ℤ) :
    torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
      s(![x, 0], ![x, 1]) ≠ true := by
  intro hopen
  have h := (thinTranslationClosureCounterexample_vertical_iff x 0).mp hopen
  rcases h.2 with h | h | h | h
  · exact (by decide : (0 : ZMod 8) ≠ 1) h
  · exact (by decide : (0 : ZMod 8) ≠ 2) h
  · exact (by decide : (0 : ZMod 8) ≠ 3) h
  · exact (by decide : (0 : ZMod 8) ≠ 4) h


theorem thinTranslationClosureCounterexample_cut_five (x : ℤ) :
    torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
      s(![x, 5], ![x, 6]) ≠ true := by
  intro hopen
  have h := (thinTranslationClosureCounterexample_vertical_iff x 5).mp hopen
  rcases h.2 with h | h | h | h
  · exact (by decide : (5 : ZMod 8) ≠ 1) h
  · exact (by decide : (5 : ZMod 8) ≠ 2) h
  · exact (by decide : (5 : ZMod 8) ≠ 3) h
  · exact (by decide : (5 : ZMod 8) ≠ 4) h


theorem thinTranslationClosureCounterexample_not_coarse :
    ¬ bdcTorusThinCrossing 8 2 1
      thinTranslationClosureCounterexampleConfig := by
  rintro ⟨k, hk⟩
  let a : ℤ := bdcLongRectangleXOffset 1 k
  let c : ℤ := bdcLongRectangleYOffset 1 k
  change VerticalCrossing
    (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig)
      a (a + 2) c (c + 4) at hk
  have hc : c = 0 ∨ c = 4 := by
    simp [c, bdcLongRectangleYOffset]
    omega
  rcases hc with hc | hc
  · rw [hc] at hk
    apply thinTranslationClosureCounterexample_no_vertical_of_cut
      (a := a) (c := 0) (h := 0)
      (by norm_num) (by norm_num)
      thinTranslationClosureCounterexample_cut_zero
    simpa [a] using hk
  · rw [hc] at hk
    apply thinTranslationClosureCounterexample_no_vertical_of_cut
      (a := a) (c := 4) (h := 5)
      (by norm_num) (by norm_num)
      thinTranslationClosureCounterexample_cut_five
    simpa [a] using hk


theorem thinTranslationClosureCounterexample_closure_not_coarse :
    bdcTorusThinCrossingTranslationClosure 8 2 1
        thinTranslationClosureCounterexampleConfig ∧
      ¬ bdcTorusThinCrossing 8 2 1
        thinTranslationClosureCounterexampleConfig :=
  ⟨thinTranslationClosureCounterexample_mem_closure,
    thinTranslationClosureCounterexample_not_coarse⟩


theorem not_translationClosure_coarseCover_two_one :
    ¬ BdcTorusWindingToThinCover 8 2 1
      (bdcTorusThinCrossingTranslationClosureEvent 8 2 1) := by
  intro h
  exact thinTranslationClosureCounterexample_not_coarse
    (h.toThin thinTranslationClosureCounterexampleConfig
      thinTranslationClosureCounterexample_mem_closure)

end StatMech.BeffaraDC
