/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part2
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

theorem ons_int_bounds_of_natAbs_le {n : Nat} {z : Int}
    (hz : z.natAbs <= n) : -(n : Int) <= z ∧ z <= n := by
  rcases Int.natAbs_eq z with hz' | hz' <;> omega

theorem ons_natAbs_le_of_int_bounds {n : Nat} {z : Int}
    (hlo : -(n : Int) <= z) (hi : z <= n) : z.natAbs <= n := by
  rcases Int.natAbs_eq z with hz | hz <;> omega

theorem ons_site_mem_plusDualFaceBox
    (n : Nat) {a b : Int}
    (ha : -(n : Int) - 1 <= a ∧ a <= n)
    (hb : -(n : Int) - 1 <= b ∧ b <= n) :
    (![a, b] : Site 2) ∈ ons_plusDualFaceBox n := by
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

theorem ons_site_mem_box_two
    (n : Nat) {a b : Int}
    (ha : -(n : Int) <= a ∧ a <= n)
    (hb : -(n : Int) <= b ∧ b <= n) :
    (![a, b] : Site 2) ∈ box 2 n := by
  rw [mem_box]
  intro i
  fin_cases i
  · simpa using ons_natAbs_le_of_int_bounds ha.1 ha.2
  · simpa using ons_natAbs_le_of_int_bounds hb.1 hb.2

theorem ons_flankFaces_mem_plusDualFaceBox_of_left
    (n : Nat) {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (hp : p ∈ box 2 n) :
    forall f, f ∈ flankFaces p q -> f ∈ ons_plusDualFaceBox n := by
  intro f hf
  have hp0 := ons_int_bounds_of_natAbs_le (hp 0)
  have hp1 := ons_int_bounds_of_natAbs_le (hp 1)
  rcases adj_cases hadj with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · unfold flankFaces at hf
    rw [if_pos h0, Sym2.mem_iff] at hf
    rcases hf with rfl | rfl
    · apply ons_site_mem_plusDualFaceBox n
      · omega
      · rcases hy with hpq | hqp <;> omega
    · apply ons_site_mem_plusDualFaceBox n
      · omega
      · rcases hy with hpq | hqp <;> omega
  · unfold flankFaces at hf
    rw [if_neg (by intro hpq; omega), Sym2.mem_iff] at hf
    rcases hf with rfl | rfl
    · apply ons_site_mem_plusDualFaceBox n
      · rcases hx with hpq | hqp <;> omega
      · omega
    · apply ons_site_mem_plusDualFaceBox n
      · rcases hx with hpq | hqp <;> omega
      · omega

theorem ons_flankFaces_mem_plusDualFaceBox
    (n : Nat) {p q : Site 2} (hadj : (hypercubicLattice 2).Adj p q)
    (htouch : p ∈ box 2 n ∨ q ∈ box 2 n) :
    forall f, f ∈ flankFaces p q -> f ∈ ons_plusDualFaceBox n := by
  rcases htouch with hp | hq
  · exact ons_flankFaces_mem_plusDualFaceBox_of_left n hadj hp
  · rw [flankFaces_comm]
    exact ons_flankFaces_mem_plusDualFaceBox_of_left n hadj.symm hq


theorem ons_flankFacesSym_mem_plusDualFaceEdgeSet
    (n : Nat) {edge : Sym2 (Site 2)}
    (hedge : edge ∈ bondFinsetTouch 2 n) :
    flankFacesSym edge ∈ ons_plusDualFaceEdgeSet n := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
      have hdata := hedge
      rw [bondFinsetTouch, Finset.mem_image] at hdata
      obtain ⟨⟨p', q'⟩, hpq, heq⟩ := hdata
      rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product] at hpq
      have hadj : (hypercubicLattice 2).Adj p q :=
        adj_of_mem_bondFinsetTouch hedge
      have htouch : p ∈ box 2 n ∨ q ∈ box 2 n := by
        have hs : s(p', q') = s(p, q) := heq
        rw [Sym2.eq_iff] at hs
        rcases hs with hs | hs
        · simpa [hs.1, hs.2] using hpq.2.2
        · simpa [hs.1, hs.2, or_comm] using hpq.2.2
      refine ⟨?_, ?_⟩
      · obtain ⟨f, g, hfg, hfgadj⟩ := flankFaces_latAdj hadj
        rw [flankFacesSym_mk, hfg, SimpleGraph.mem_edgeSet]
        exact hfgadj
      · simpa only [flankFacesSym_mk] using
          ons_flankFaces_mem_plusDualFaceBox n hadj htouch

theorem ons_symPrimal_mem_box_touch
    (n : Nat) {f g : Site 2} (hadj : (hypercubicLattice 2).Adj f g)
    (hf : f ∈ ons_plusDualFaceBox n) (hg : g ∈ ons_plusDualFaceBox n) :
    symPrimal f g ∈ bondFinsetTouch 2 n := by
  rcases adj_cases hadj with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · unfold symPrimal
    rw [if_pos h0]
    apply mk_mem_bondFinsetTouch
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
        latAdj_right (f 0) (max (f 1) (g 1))
    · have hf0 := hf 0
      have hf1 := hf 1
      have hg1 := hg 1
      have hmax : -(n : Int) <= max (f 1) (g 1) ∧
          max (f 1) (g 1) <= n := by
        rcases hy with hfg | hgf <;> constructor <;> omega
      by_cases hlow : f 0 < -(n : Int)
      · right
        exact ons_site_mem_box_two n ⟨by omega, by omega⟩ hmax
      · left
        exact ons_site_mem_box_two n ⟨by omega, by omega⟩ hmax
  · unfold symPrimal
    rw [if_neg (by intro h0; omega)]
    apply mk_mem_bondFinsetTouch
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
        latAdj_top (max (f 0) (g 0)) (min (f 1) (g 1))
    · have hf0 := hf 0
      have hg0 := hg 0
      have hf1 := hf 1
      have hmax : -(n : Int) <= max (f 0) (g 0) ∧
          max (f 0) (g 0) <= n := by
        rcases hx with hfg | hgf <;> constructor <;> omega
      rw [h1]
      by_cases hlow : g 1 < -(n : Int)
      · right
        exact ons_site_mem_box_two n hmax ⟨by omega, by omega⟩
      · left
        exact ons_site_mem_box_two n hmax ⟨by omega, by omega⟩


theorem ons_symPrimalSym_mem_bondFinsetTouch
    (n : Nat) {edge : Sym2 (Site 2)}
    (hedge : edge ∈ ons_plusDualFaceEdgeSet n) :
    symPrimalSym edge ∈ bondFinsetTouch 2 n := by
  rcases hedge with ⟨hadj, hsupp⟩
  induction edge using Sym2.inductionOn with
  | _ f g =>
      rw [SimpleGraph.mem_edgeSet] at hadj
      exact ons_symPrimal_mem_box_touch n hadj
        (hsupp f (Sym2.mem_mk_left f g))
        (hsupp g (Sym2.mem_mk_right f g))


end
end StatMech.Onsager
