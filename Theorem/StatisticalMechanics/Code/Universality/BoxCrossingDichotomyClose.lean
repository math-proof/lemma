/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Def.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem bcc_site_eq_x0 {a : Site 2} (ha0 : a 0 = 0) : a = ![0, a 1] := by
  funext i; fin_cases i
  · simpa using ha0
  · simp


theorem bcc_site_eq_x1 {b : Site 2} (hb0 : b 0 = 1) {c : ℤ} (h1 : b 1 = c) : b = ![1, c] := by
  funext i; fin_cases i
  · simpa using hb0
  · simpa using h1


theorem bcc_is_wall_edge {a b : Site 2} (ha0 : a 0 = 0) (hb0 : b 0 = 1) (h1 : a 1 = b 1)
    (hc : a 1 = 0 ∨ a 1 = 1 ∨ a 1 = 2) :
    s(a, b) = s(![0,0],![1,0]) ∨ s(a, b) = s(![0,1],![1,1]) ∨ s(a, b) = s(![0,2],![1,2]) := by
  have hae : a = ![0, a 1] := bcc_site_eq_x0 ha0
  have hbe : b = ![1, a 1] := bcc_site_eq_x1 hb0 h1.symm
  rcases hc with h | h | h
  · left; rw [hae, hbe, h]
  · right; left; rw [hae, hbe, h]
  · right; right; rw [hae, hbe, h]


theorem bcc_wall_open_keeps_x0 {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (ha : a ∈ rect 0 2 0 2) (hb : b ∈ rect 0 2 0 2)
    (hopen : bcc_wallCfg s(a, b) = true) : (a 0 = 0 ↔ b 0 = 0) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab
  rw [mem_rect] at ha hb
  by_contra hne
  have hx : a 0 ≠ b 0 := by intro h; rw [h] at hne; exact hne Iff.rfl
  have h1 : a 1 = b 1 := by omega
  have hcase : (a 0 = 0 ∧ b 0 = 1) ∨ (a 0 = 1 ∧ b 0 = 0) := by omega
  have heq : s(a,b) = s(![0,0],![1,0]) ∨ s(a,b) = s(![0,1],![1,1]) ∨ s(a,b) = s(![0,2],![1,2]) := by
    rcases hcase with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩
    · exact bcc_is_wall_edge ha0 hb0 h1 (by omega)
    · rw [Sym2.eq_swap]; exact bcc_is_wall_edge hb0 ha0 h1.symm (by omega)
  rcases heq with h | h | h <;> (rw [h] at hopen; simp [bcc_wallCfg] at hopen)


theorem bcc_wall_walk_keeps_x0 {x y : (rect 0 2 0 2 : Set (Site 2))}
    (w : (openSubgraphInduce 2 bcc_wallCfg (rect 0 2 0 2)).Walk x y) :
    ((x : Site 2) 0 = 0 ↔ (y : Site 2) 0 = 0) := by
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact (bcc_wall_open_keeps_x0 hab.1 a.2 b.2 hab.2).trans ih


theorem bcc_noH_wall : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
  rintro ⟨x, y, hxy⟩
  have hinv := bcc_wall_walk_keeps_x0 (x := ⟨(x:Site 2), leftSide_subset x.2⟩)
    (y := ⟨(y:Site 2), rightSide_subset y.2⟩) hxy.some
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = 2 := y.2.2
  rw [hy0] at hinv
  have : (2:ℤ) = 0 := hinv.mp hx0
  norm_num at this


theorem bcc_wallCfg_false_iff (e : Sym2 (Site 2)) :
    bcc_wallCfg e = false ↔
      (e = s(![0,0],![1,0]) ∨ e = s(![0,1],![1,1]) ∨ e = s(![0,2],![1,2])) := by
  unfold bcc_wallCfg
  rw [Bool.not_eq_false', Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    decide_eq_true_eq, decide_eq_true_eq, or_assoc]


theorem bcc_crossEdge_symm_mk (x y : Site 2) :
    crossEdge.symm s(x, y) = s(rot90Inv x, rot90Inv y) := by
  simp [crossEdge, sym2Congr]


theorem bcc_dualOpen_char {p q : Site 2} (h : dualConfig bcc_wallCfg s(p, q) = true) :
    s(rot90Inv p, rot90Inv q) = s(![0,0],![1,0]) ∨
    s(rot90Inv p, rot90Inv q) = s(![0,1],![1,1]) ∨
    s(rot90Inv p, rot90Inv q) = s(![0,2],![1,2]) := by
  rw [dual_isOpen_iff_isClosed, bcc_crossEdge_symm_mk] at h
  exact (bcc_wallCfg_false_iff _).mp h


theorem bcc_rot90Inv_fst (p : Site 2) : (rot90Inv p) 0 = p 1 := by simp [rot90Inv]


theorem bcc_dualOpen_snd_le {p q : Site 2} (h : dualConfig bcc_wallCfg s(p, q) = true) :
    p 1 ≤ 1 ∧ q 1 ≤ 1 := by
  have hc := bcc_dualOpen_char h
  have key : ∀ {r1 r2 : Site 2},
      s(r1, r2) = s(![0,(0:ℤ)],![1,0]) ∨ s(r1,r2) = s(![0,(1:ℤ)],![1,1]) ∨
        s(r1,r2) = s(![0,(2:ℤ)],![1,2]) →
      (r1 0 = 0 ∨ r1 0 = 1) ∧ (r2 0 = 0 ∨ r2 0 = 1) := by
    intro r1 r2 hr
    rcases hr with h | h | h <;>
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2 <;> refine ⟨by simp, by simp⟩
  obtain ⟨hp, hq⟩ := key hc
  rw [bcc_rot90Inv_fst] at hp hq
  exact ⟨by omega, by omega⟩


theorem bcc_dualVwalk_keeps_snd {x y : (rect 0 2 0 2 : Set (Site 2))}
    (w : (openSubgraphInduce 2 (dualConfig bcc_wallCfg) (rect 0 2 0 2)).Walk x y)
    (hx : (x : Site 2) 1 ≤ 1) : (y : Site 2) 1 ≤ 1 := by
  induction w with
  | nil => exact hx
  | @cons a b c hab p ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact ih (bcc_dualOpen_snd_le hab.2).2


theorem bcc_noV_wall : ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 := by
  rintro ⟨x, y, hxy⟩
  have hx1 : (x : Site 2) 1 = 0 := x.2.2
  have hy1 : (y : Site 2) 1 = 2 := y.2.2
  have hinv := bcc_dualVwalk_keeps_snd (x := ⟨(x:Site 2), bottomSide_subset x.2⟩)
    (y := ⟨(y:Site 2), topSide_subset y.2⟩) hxy.some (by rw [hx1]; norm_num)
  rw [hy1] at hinv
  norm_num at hinv


theorem bcc_wall_noH_noV :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall⟩


theorem bcc_dichotomy_false :
    ¬ ((horizontalCrossingEvent 0 2 0 2)ᶜ ⊆ dualVerticalCrossingEvent 0 2 0 2) := by
  intro hsub
  have hmem : bcc_wallCfg ∈ (horizontalCrossingEvent 0 2 0 2)ᶜ := by
    rw [Set.mem_compl_iff, mem_horizontalCrossingEvent]; exact bcc_noH_wall
  have hdv : bcc_wallCfg ∈ dualVerticalCrossingEvent 0 2 0 2 := hsub hmem
  rw [mem_dualVerticalCrossingEvent] at hdv
  exact bcc_noV_wall hdv


end Universality
end StatMech
