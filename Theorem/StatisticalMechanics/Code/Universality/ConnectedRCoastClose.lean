/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_rightComplement_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c c' : Site 2}
    (hc : c ∈ bac_rightComplement ω n) (hadj : (hypercubicLattice 2).Adj c c')
    (hc'box : c' ∈ rect 0 n 0 n) (hc'L : c' ∉ bcd_leftReach ω n) :
    c' ∈ bac_rightComplement ω n := by
  obtain ⟨hcc, y, hyR, hyc, hreach⟩ := hc
  have hc'c : c' ∈ bac_boxMinusL ω n := ⟨hc'box, hc'L⟩
  refine ⟨hc'c, y, hyR, hyc, ?_⟩
  have hstep : ((hypercubicLattice 2).induce (bac_boxMinusL ω n)).Adj ⟨c', hc'c⟩ ⟨c, hcc⟩ := by
    simp only [SimpleGraph.induce_adj]; exact hadj.symm
  exact (hstep.reachable).trans hreach


theorem crr_horizInterface_flank0_isRCoast (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
    (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    bac_IsRCoastFace ω n ![x, y] := by
  refine ⟨⟨![x, y - 1], rcm_horizEdge_faces_pmdAdj ω n hbd hp hq⟩, ![x + 1, y], hqR, ?_⟩
  right; left; simp


theorem crr_horizInterface_flank1_isRCoast (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {x y : ℤ}
    (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
    (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
    (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n) (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
    bac_IsRCoastFace ω n ![x, y - 1] := by
  refine ⟨⟨![x, y], (rcm_horizEdge_faces_pmdAdj ω n hbd hp hq).symm⟩, ![x + 1, y], hqR, ?_⟩
  right; right; right; simp


theorem crr_face_nbr_cases (a b : ℤ) (g : Site 2) (hadj : (hypercubicLattice 2).Adj ![a, b] g) :
    g = ![a + 1, b] ∨ g = ![a - 1, b] ∨ g = ![a, b + 1] ∨ g = ![a, b - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hadj
  have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> simp
  have key : ((a - g 0).natAbs = 1 ∧ (b - g 1).natAbs = 0) ∨
             ((a - g 0).natAbs = 0 ∧ (b - g 1).natAbs = 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hb : g 1 = b := by omega
    rcases Int.natAbs_eq (a - g 0) with he | he
    · right; left; rw [hg, show g 0 = a - 1 by omega, hb]
    · left; rw [hg, show g 0 = a + 1 by omega, hb]
  · have ha : g 0 = a := by omega
    rcases Int.natAbs_eq (b - g 1) with he | he
    · right; right; right; rw [hg, show g 1 = b - 1 by omega, ha]
    · right; right; left; rw [hg, show g 1 = b + 1 by omega, ha]


theorem crr_face_barrier_side (ω : ConfigSpace (Sym2 (Site 2))) (n a b : ℤ)
    (h : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj ![a, b] g) :
    ∃ u v : Site 2,
      ((u = ![a, b] ∧ v = ![a + 1, b]) ∨ (u = ![a, b + 1] ∧ v = ![a + 1, b + 1]) ∨
        (u = ![a, b] ∧ v = ![a, b + 1]) ∨ (u = ![a + 1, b] ∧ v = ![a + 1, b + 1])) ∧
      bdEdge (bcd_leftReach ω n) s(u, v) ∧ u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
  obtain ⟨g, hadj, p, q, hpq, hbd, hp, hq⟩ := h
  
  have finish : ∀ u v : Site 2, sharedPrimalEdge ![a, b] g = s(u, v) →
      bdEdge (bcd_leftReach ω n) s(u, v) ∧ u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v hs
    rw [hs] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · exact ⟨hbd, hp, hq⟩
    · exact ⟨by rwa [Sym2.eq_swap], hq, hp⟩
  rcases crr_face_nbr_cases a b g hadj with hg | hg | hg | hg <;> subst hg
  · refine ⟨![a + 1, b], ![a + 1, b + 1], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_right]; rfl
  · refine ⟨![a, b], ![a, b + 1], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_left]; rfl
  · refine ⟨![a, b + 1], ![a + 1, b + 1], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_top]; rfl
  · refine ⟨![a, b], ![a + 1, b], by tauto, finish _ _ ?_⟩
    rw [sharedPrimalEdge_bottom]; rfl


theorem crr_nbr_of_rCorner (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c c' : Site 2}
    (hc : c ∈ bac_rightComplement ω n) (hadj : (hypercubicLattice 2).Adj c c')
    (hc'box : c' ∈ rect 0 n 0 n) :
    c' ∈ bcd_leftReach ω n ∨ c' ∈ bac_rightComplement ω n := by
  by_cases hL : c' ∈ bcd_leftReach ω n
  · exact Or.inl hL
  · exact Or.inr (crr_rightComplement_closed ω n hc hadj hc'box hL)


end Universality
end StatMech
