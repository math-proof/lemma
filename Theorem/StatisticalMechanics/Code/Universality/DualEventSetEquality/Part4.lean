/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part3
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem des_cutConfig_cut_closed (b : ℤ) : des_cutConfig s(![0, b], ![1, b]) = false := by
  classical
  simp only [des_cutConfig, decide_eq_false_iff_not, not_not]
  exact ⟨b, rfl⟩


theorem des_cutConfig_open_of_not_cut {e : Sym2 (Site 2)}
    (h : ¬ ∃ b : ℤ, e = s(![0, b], ![1, b])) : des_cutConfig e = true := by
  classical
  simp only [des_cutConfig, decide_eq_true_eq]
  exact h


theorem des_cross_edge_is_cut {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u 0 = 0) (hv : v 0 = 1) : s(u, v) = s(![0, u 1], ![1, u 1]) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two, hu, hv] at hadj
  set b := u 1 with hb
  have h1 : b = v 1 := by
    have : (b - v 1).natAbs = 0 := by omega
    omega
  have hue : u = ![0, b] := by
    funext i; fin_cases i
    · simpa using hu
    · simp [← hb]
  have hve : v = ![1, b] := by
    funext i; fin_cases i
    · simpa using hv
    · simp [h1]
  rw [hue, hve]


theorem des_cutConfig_no_cross {u v : Site 2}
    (h : IsOpenEdge 2 des_cutConfig u v) (hu : u 0 = 0) (hv : v 0 = 1) : False := by
  obtain ⟨hadj, hopen⟩ := h
  rw [des_cross_edge_is_cut hadj hu hv, des_cutConfig_cut_closed] at hopen
  exact absurd hopen (by simp)


theorem des_cutConfig_open_sameSide0 {u v : Site 2}
    (h : IsOpenEdge 2 des_cutConfig u v) : (u 0 ≤ 0 ↔ v 0 ≤ 0) := by
  have hadj' := h.1
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  have hbound : (u 0 - v 0).natAbs ≤ 1 := by omega
  constructor
  · intro hu
    by_contra hv
    
    have hu0 : u 0 = 0 := by omega
    have hv1 : v 0 = 1 := by omega
    exact des_cutConfig_no_cross h hu0 hv1
  · intro hv
    by_contra hu
    have hv0 : v 0 = 0 := by omega
    have hu1 : u 0 = 1 := by omega
    exact des_cutConfig_no_cross (isOpenEdge_symm h) hv0 hu1


theorem des_cutConfig_connectedWithin_sameSide0 {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 des_cutConfig S x y) : ((x : Site 2) 0 ≤ 0 ↔ (y : Site 2) 0 ≤ 0) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact (des_cutConfig_open_sameSide0 hab).trans ih


theorem des_cutConfig_no_H (n : ℤ) (hn : 1 ≤ n) :
    ¬ HorizontalCrossing des_cutConfig 0 n 0 n := by
  rintro ⟨x, y, hxy⟩
  have hside := des_cutConfig_connectedWithin_sameSide0 hxy
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = n := y.2.2
  rw [hx0, hy0] at hside
  have : (0 : ℤ) ≤ 0 := le_refl 0
  have : (n : ℤ) ≤ 0 := hside.mp this
  omega


theorem des_negCut_open_le_one {u v : Site 2}
    (h : IsOpenEdge 2 (des_negConfig des_cutConfig) u v) : u 0 ≤ 1 ∧ v 0 ≤ 1 := by
  obtain ⟨hadj, hopen⟩ := h
  
  rw [des_negConfig_open_iff_closed] at hopen
  
  by_contra hcon
  apply absurd hopen
  rw [des_cutConfig_open_of_not_cut]
  · simp
  · rintro ⟨c, hc⟩
    
    rw [Sym2.eq_iff] at hc
    push Not at hcon
    rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · subst hu; subst hv; simp at hcon
    · subst hu; subst hv; simp at hcon


theorem des_negCut_connectedWithin_le_one {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (des_negConfig des_cutConfig) S x y)
    (hx : (x : Site 2) 0 ≤ 1) : (y : Site 2) 0 ≤ 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact ih (des_negCut_open_le_one hab).2


theorem des_cutConfig_no_negH (n : ℤ) (hn : 2 ≤ n) :
    ¬ HorizontalCrossing (des_negConfig des_cutConfig) 0 n (-n) 0 := by
  rintro ⟨x, y, hxy⟩
  have hx1 : ((⟨(x : Site 2), leftSide_subset x.2⟩ : rect 0 n (-n) 0) : Site 2) 0 ≤ 1 := by
    show (x : Site 2) 0 ≤ 1; rw [x.2.2]; norm_num
  have hy1 := des_negCut_connectedWithin_le_one hxy hx1
  have : (y : Site 2) 0 ≤ 1 := hy1
  rw [y.2.2] at this
  omega


theorem des_hsepSquare_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) := by
  rw [des_hsepSquare_iff_closedH_rotbox]
  intro h
  exact des_cutConfig_no_negH n hn (h des_cutConfig (des_cutConfig_no_H n (by omega)))

end Universality
end StatMech
