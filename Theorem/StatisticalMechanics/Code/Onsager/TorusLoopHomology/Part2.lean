/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter.Part2
import Def.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part3


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_portEdge_loop_injective {L n : ℕ}
    [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    Function.Injective (fun k => ons_portEdge L (d k)) := by
  intro i j hij
  rcases (ons_portEdge_eq_iff L (d j) (d i)).mp hij with hsame | hrev
  · exact hsite (congrArg Prod.fst hsame)
  · have hj : j - 1 + 1 = j := by abel
    have hsites : (d i).1 = (d (j - 1)).1 := by
      calc
        (d i).1 = (ons_dartRev L (d j)).1 := congrArg Prod.fst hrev
        _ = ons_dirStep L (d j).2 (d j).1 := rfl
        _ = (d (j - 1)).1 := by
          have h := hvalid (j - 1)
          rw [hj] at h
          exact h.symm
    have hi : i = j - 1 := hsite hsites
    have hdir := congrArg Prod.snd hrev
    subst i
    exfalso
    apply (hnu (j - 1))
    rw [hj]
    simpa only [ons_dartRev] using hdir

theorem ons_dartEdgeSet_filter_x {L n : ℕ} [Fact (2 < L)]
    (d : Fin n → ons_Dart L) :
    (ons_dartEdgeSet d).filter (ons_xSeamEdge L) =
      (Finset.univ.filter (fun k => ons_xWrap (d k))).image
        (fun k => ons_portEdge L (d k)) := by
  classical
  ext edge
  simp only [ons_dartEdgeSet, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, hk⟩, hseam⟩
    refine ⟨k, ?_, hk⟩
    rw [← hk] at hseam
    exact (ons_xSeamEdge_portEdge_iff (d k)).mp hseam
  · rintro ⟨k, hwrap, hk⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← hk]
    exact (ons_xSeamEdge_portEdge_iff (d k)).mpr hwrap

theorem ons_dartEdgeSet_filter_y {L n : ℕ} [Fact (2 < L)]
    (d : Fin n → ons_Dart L) :
    (ons_dartEdgeSet d).filter (ons_ySeamEdge L) =
      (Finset.univ.filter (fun k => ons_yWrap (d k))).image
        (fun k => ons_portEdge L (d k)) := by
  classical
  ext edge
  simp only [ons_dartEdgeSet, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, hk⟩, hseam⟩
    refine ⟨k, ?_, hk⟩
    rw [← hk] at hseam
    exact (ons_ySeamEdge_portEdge_iff (d k)).mp hseam
  · rintro ⟨k, hwrap, hk⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [← hk]
    exact (ons_ySeamEdge_portEdge_iff (d k)).mpr hwrap

theorem ons_dartEdgeSet_xSeam_card {L n : ℕ}
    [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    ((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card =
      (Finset.univ.filter (fun k => ons_xWrap (d k))).card := by
  rw [ons_dartEdgeSet_filter_x]
  exact Finset.card_image_iff.mpr
    ((ons_portEdge_loop_injective d hvalid hsite hnu).injOn)

theorem ons_dartEdgeSet_ySeam_card {L n : ℕ}
    [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    ((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card =
      (Finset.univ.filter (fun k => ons_yWrap (d k))).card := by
  rw [ons_dartEdgeSet_filter_y]
  exact Finset.card_image_iff.mpr
    ((ons_portEdge_loop_injective d hvalid hsite hnu).injOn)

theorem ons_intParity_eq_zmod (m : ℤ) :
    ons_intParity m = (m : ZMod 2) := by
  apply Fin.ext
  by_cases hm : Even m
  · simp only [ons_intParity, if_pos hm, Fin.val_zero]
    have hz : (m : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact even_iff_two_dvd.mp hm
    have hv := congrArg ZMod.val hz
    simpa using hv.symm
  · have ho := Int.not_even_iff_odd.mp hm
    simp only [ons_intParity, if_neg hm, Fin.val_one]
    rcases ho with ⟨k, rfl⟩
    have htwo : (2 : ZMod 2) = 0 := by decide
    have hz : (((2 * k + 1 : ℤ) : ZMod 2)) = 1 := by
      push_cast
      rw [htwo, zero_mul, zero_add]
    have hv := congrArg ZMod.val hz
    simpa using hv.symm

theorem ons_xWrapSign_cast (d : ons_Dart L) :
    ((ons_xWrapSign d : ℤ) : ZMod 2) =
      if ons_xWrap d then 1 else 0 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_xWrapSign, ons_xWrap]

theorem ons_yWrapSign_cast (d : ons_Dart L) :
    ((ons_yWrapSign d : ℤ) : ZMod 2) =
      if ons_yWrap d then 1 else 0 := by
  rcases d with ⟨p, mu⟩
  fin_cases mu <;> simp [ons_yWrapSign, ons_yWrap]

theorem ons_intParity_sum_xWrapSign {L n : ℕ}
    (d : Fin n → ons_Dart L) :
    ons_intParity (∑ k, ons_xWrapSign (d k)) =
      ⟨(Finset.univ.filter (fun k => ons_xWrap (d k))).card % 2,
        Nat.mod_lt _ (by decide)⟩ := by
  rw [ons_intParity_eq_zmod]
  apply Fin.ext
  rw [Int.cast_sum]
  simp_rw [ons_xWrapSign_cast]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ZMod.val_natCast 2 _

theorem ons_intParity_sum_yWrapSign {L n : ℕ}
    (d : Fin n → ons_Dart L) :
    ons_intParity (∑ k, ons_yWrapSign (d k)) =
      ⟨(Finset.univ.filter (fun k => ons_yWrap (d k))).card % 2,
        Nat.mod_lt _ (by decide)⟩ := by
  rw [ons_intParity_eq_zmod]
  apply Fin.ext
  rw [Int.cast_sum]
  simp_rw [ons_yWrapSign_cast]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ZMod.val_natCast 2 _


theorem ons_evenHomology_dartEdgeSet_eq_windingParity
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
    (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my) :
    ons_evenHomology L (ons_dartEdgeSet d) =
      ons_windingParity mx my := by
  have hL : (L : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
      (Fact.out : 2 < L)))
  have hxwrap := ons_sum_dirExponentX_eq_wrap d hvalid
  have hywrap := ons_sum_dirExponentY_eq_wrap d hvalid
  have hx : mx = ∑ k, ons_xWrapSign (d k) := by
    apply mul_left_cancel₀ hL
    exact hmx.symm.trans hxwrap
  have hy : my = ∑ k, ons_yWrapSign (d k) := by
    apply mul_left_cancel₀ hL
    exact hmy.symm.trans hywrap
  apply Prod.ext
  · change
      ⟨((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card % 2,
          Nat.mod_lt _ (by decide)⟩ = ons_intParity mx
    rw [ons_dartEdgeSet_xSeam_card d hvalid hsite hnu, hx]
    exact (ons_intParity_sum_xWrapSign d).symm
  · change
      ⟨((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card % 2,
          Nat.mod_lt _ (by decide)⟩ = ons_intParity my
    rw [ons_dartEdgeSet_ySeam_card d hvalid hsite hnu, hy]
    exact (ons_intParity_sum_yWrapSign d).symm

theorem ons_dartEdgeSet_card {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    (ons_dartEdgeSet d).card = n := by
  rw [ons_dartEdgeSet, Finset.card_image_iff.mpr
    ((ons_portEdge_loop_injective d hvalid hsite hnu).injOn),
    Finset.card_univ, Fintype.card_fin]


theorem ons_loopWeight_spinPhase_eq_homology
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (x omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      ons_spinLinearCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) *
        ons_loopWeight (ons_KWmat L x omega) d := by
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists d hvalid
  rw [ons_loopWeight_spinPhase_of_winding x omega a b d mx my hmx hmy,
    ons_spinPhase_character]
  rw [ons_evenHomology_dartEdgeSet_eq_windingParity
    d hvalid hsite hnu mx my hmx hmy]


theorem ons_loopWeight_spinPhase_eq_spinCharacter
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (x omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hsite : Function.Injective (fun k => (d k).1))
    (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
    (hgeom : ons_loopWeight (ons_KWmat L x omega) d =
      -(ons_spinCharacter 0 0
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n := by
  rw [ons_loopWeight_spinPhase_eq_homology
    x omega a b d hvalid hsite hnu, hgeom]
  have hchar := ons_spinLinear_mul_quadratic a b
    (ons_evenHomology L (ons_dartEdgeSet d))
  calc
    ons_spinLinearCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) *
        (-(ons_spinCharacter 0 0
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n) =
      -(ons_spinLinearCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) *
        (ons_spinCharacter 0 0
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ)) * x ^ n := by ring
    _ = -(ons_spinCharacter a b
          (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n := by
      rw [hchar]

end StatMech.Onsager
