/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveResidue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusResiduePotential
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.TorusPrimitiveResidue.Part3
open scoped BigOperators


namespace StatMech.Onsager

open StatMech.FrontierD

open StatMech.FrontierD.IntegralSquareTorusCycle

noncomputable section

theorem ons_residueLoopCoeff_pred
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [NeZero p]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
    (hy : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1))
    (k : Fin n) :
    ons_residueLoopCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p v k =
      ons_residueLoopCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p v
        (k - 1) := by
  let C := IntegralSquareTorusCycle.ofDarts v hvalid
  let a := ons_liftDir v k
  let b := ons_liftDir v (k - 1) + 2
  have hab : a ≠ b := by
    have h := ons_liftDir_nonUturn v hnu (k - 1)
    simpa [a, b] using h
  have hzero : ∀ mu, mu ≠ a → mu ≠ b →
      ons_residueOutgoingCoeff C p (ons_liftSite v k) mu = 0 := by
    intro mu hma hmb
    apply ons_residueOutgoingCoeff_eq_zero_of_not_mem
      v hvalid hx hy
    intro hmem
    have hm := (ons_portEdge_mem_dartEdgeSet_at_liftSite_iff
      v hvalid hsite k mu).mp hmem
    exact hm.elim hma hmb
  have hdiv := ons_residueOutgoingCoeff_divergence
    C p (ons_liftSite v k)
  rw [ons_fin4_sum_eq_two
    (fun mu ↦ ons_residueOutgoingCoeff C p (ons_liftSite v k) mu)
    a b hab hzero] at hdiv
  have hincoming :
      ons_residueOutgoingCoeff C p (ons_liftSite v k) b =
        -ons_residueLoopCoeff C p v (k - 1) := by
    have hd := ons_liftSite_incomingRevDart v hvalid k
    have hr := ons_residueOutgoingCoeff_dartRev C p (v (-k + 1))
    rw [← hd] at hr
    have hidx : -k + 1 = 1 - k := by abel
    rw [hidx] at hr
    simpa [b, ons_residueLoopCoeff, ons_liftSite, ons_liftDir] using hr
  change ons_residueOutgoingCoeff C p (ons_liftSite v k) a = _
  rw [hincoming] at hdiv
  linear_combination hdiv

theorem ons_residueLoopCoeff_constant
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [NeZero p]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
    (hy : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
    ∀ k, ons_residueLoopCoeff
        (IntegralSquareTorusCycle.ofDarts v hvalid) p v k =
      ons_residueLoopCoeff
        (IntegralSquareTorusCycle.ofDarts v hvalid) p v 0 := by
  apply ons_fin_pred_invariant
  exact ons_residueLoopCoeff_pred v hvalid hsite hnu hx hy

theorem IntegralSquareTorusCycle.ofDarts_horizontal_eq_single_of_portEdge
    {L n : Nat} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (k : Fin n) (z : ZMod L × ZMod L)
    (hport : ons_portEdge L (v k) = ons_portEdge L (z, 0)) :
    (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z =
      IntegralSquareTorusCycle.dartHorizontal (v k) z := by
  change (∑ j, IntegralSquareTorusCycle.dartHorizontal (v j) z) = _
  apply Finset.sum_eq_single k
  · intro j _ hjk
    by_contra hj
    have hjport := ons_portEdge_eq_of_dartHorizontal_ne_zero (v j) z hj
    have hindex := ons_portEdge_loop_injective v hvalid hsite hnu
      (hjport.trans hport.symm)
    exact hjk hindex
  · simp

theorem IntegralSquareTorusCycle.ofDarts_vertical_eq_single_of_portEdge
    {L n : Nat} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (k : Fin n) (z : ZMod L × ZMod L)
    (hport : ons_portEdge L (v k) = ons_portEdge L (z, 1)) :
    (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z =
      IntegralSquareTorusCycle.dartVertical (v k) z := by
  change (∑ j, IntegralSquareTorusCycle.dartVertical (v j) z) = _
  apply Finset.sum_eq_single k
  · intro j _ hjk
    by_contra hj
    have hjport := ons_portEdge_eq_of_dartVertical_ne_zero (v j) z hj
    have hindex := ons_portEdge_loop_injective v hvalid hsite hnu
      (hjport.trans hport.symm)
    exact hjk hindex
  · simp

theorem ons_residueOutgoingCoeff_ne_zero_on_loop
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [Fact (1 < p)]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
    (hy : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1))
    (k : Fin n) :
    ons_residueOutgoingCoeff (IntegralSquareTorusCycle.ofDarts v hvalid) p
      (v k).1 (v k).2 ≠ 0 := by
  let C := IntegralSquareTorusCycle.ofDarts v hvalid
  rcases hv : v k with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · have hcurrent :=
      IntegralSquareTorusCycle.ofDarts_horizontal_eq_single_of_portEdge
        v hvalid hsite hnu k (x, y) (by simp [hv])
    have hone : C.horizontal (x, y) = 1 := by
      simpa [C, hv, IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] using hcurrent
    simpa [ons_residueOutgoingCoeff, hv] using
      C.residueHorizontalCoeff_ne_zero_of_horizontal_eq_one p hx (x, y) hone
  · have hcurrent :=
      IntegralSquareTorusCycle.ofDarts_vertical_eq_single_of_portEdge
        v hvalid hsite hnu k (x, y) (by simp [hv])
    have hone : C.vertical (x, y) = 1 := by
      simpa [C, hv, IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] using hcurrent
    simpa [ons_residueOutgoingCoeff, hv] using
      C.residueVerticalCoeff_ne_zero_of_vertical_eq_one p hy (x, y) hone
  · have hcurrent :=
      IntegralSquareTorusCycle.ofDarts_horizontal_eq_single_of_portEdge
        v hvalid hsite hnu k (x - 1, y) (by
          simpa [hv] using ons_portEdge_west_eq_horizontal L (x, y))
    have hneg : C.horizontal (x - 1, y) = -1 := by
      simpa [C, hv, IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] using hcurrent
    exact neg_ne_zero.mpr (by
      simpa [ons_residueOutgoingCoeff, hv] using
        C.residueHorizontalCoeff_ne_zero_of_horizontal_eq_neg_one
          p hx (x - 1, y) hneg)
  · have hcurrent :=
      IntegralSquareTorusCycle.ofDarts_vertical_eq_single_of_portEdge
        v hvalid hsite hnu k (x, y - 1) (by
          simpa [hv] using ons_portEdge_south_eq_vertical L (x, y))
    have hneg : C.vertical (x, y - 1) = -1 := by
      simpa [C, hv, IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] using hcurrent
    exact neg_ne_zero.mpr (by
      simpa [ons_residueOutgoingCoeff, hv] using
        C.residueVerticalCoeff_ne_zero_of_vertical_eq_neg_one
          p hy (x, y - 1) hneg)

theorem ons_residueLoopCoeff_zero_ne
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [Fact (1 < p)]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
    (hy : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
    ons_residueLoopCoeff
      (IntegralSquareTorusCycle.ofDarts v hvalid) p v 0 ≠ 0 := by
  simpa [ons_residueLoopCoeff, ons_liftSite, ons_liftDir] using
    ons_residueOutgoingCoeff_ne_zero_on_loop
      v hvalid hsite hnu hx hy (0 : Fin n)

theorem IntegralSquareTorusCycle.residueHorizontalCoeff_eq_mul_horizontal_of_loop
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [NeZero p]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
    (c : Int)
    (hc : ∀ k, ons_residueOutgoingCoeff
      (IntegralSquareTorusCycle.ofDarts v hvalid) p (v k).1 (v k).2 = c)
    (z : ZMod L × ZMod L) :
    (IntegralSquareTorusCycle.ofDarts v hvalid).residueHorizontalCoeff p z =
      c * (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z := by
  let C := IntegralSquareTorusCycle.ofDarts v hvalid
  by_cases hmem : ons_portEdge L (z, 0) ∈ ons_dartEdgeSet v
  · rw [ons_dartEdgeSet, Finset.mem_image] at hmem
    obtain ⟨k, -, hport⟩ := hmem
    have hsingle :=
      IntegralSquareTorusCycle.ofDarts_horizontal_eq_single_of_portEdge
        v hvalid hsite hnu k z hport
    have hck := hc k
    rcases (ons_portEdge_eq_iff L (z, 0) (v k)).mp hport with hsame | hrev
    · rw [hsingle, hsame]
      rw [hsame] at hck
      simpa [C, ons_residueOutgoingCoeff,
        IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] using hck
    · rw [hsingle, hrev]
      rw [hrev] at hck
      simp only [ons_dartRev] at hck ⊢
      rcases z with ⟨x, y⟩
      simp [ons_residueOutgoingCoeff, ons_dirStep,
        IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] at hck ⊢
      linear_combination -hck
  · have hcurrent :=
      IntegralSquareTorusCycle.ofDarts_horizontal_eq_zero_of_not_mem
        v hvalid z hmem
    have hresidue :=
      IntegralSquareTorusCycle.residueHorizontalCoeff_eq_zero_of_horizontal_eq_zero
        (IntegralSquareTorusCycle.ofDarts v hvalid) p hx z hcurrent
    rw [hresidue, hcurrent, mul_zero]

theorem IntegralSquareTorusCycle.residueVerticalCoeff_eq_mul_vertical_of_loop
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [NeZero p]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hy : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1))
    (c : Int)
    (hc : ∀ k, ons_residueOutgoingCoeff
      (IntegralSquareTorusCycle.ofDarts v hvalid) p (v k).1 (v k).2 = c)
    (z : ZMod L × ZMod L) :
    (IntegralSquareTorusCycle.ofDarts v hvalid).residueVerticalCoeff p z =
      c * (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z := by
  let C := IntegralSquareTorusCycle.ofDarts v hvalid
  by_cases hmem : ons_portEdge L (z, 1) ∈ ons_dartEdgeSet v
  · rw [ons_dartEdgeSet, Finset.mem_image] at hmem
    obtain ⟨k, -, hport⟩ := hmem
    have hsingle :=
      IntegralSquareTorusCycle.ofDarts_vertical_eq_single_of_portEdge
        v hvalid hsite hnu k z hport
    have hck := hc k
    rcases (ons_portEdge_eq_iff L (z, 1) (v k)).mp hport with hsame | hrev
    · rw [hsingle, hsame]
      rw [hsame] at hck
      simpa [C, ons_residueOutgoingCoeff,
        IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] using hck
    · rw [hsingle, hrev]
      rw [hrev] at hck
      simp only [ons_dartRev] at hck ⊢
      rcases z with ⟨x, y⟩
      simp [ons_residueOutgoingCoeff, ons_dirStep,
        IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] at hck ⊢
      linear_combination -hck
  · have hcurrent :=
      IntegralSquareTorusCycle.ofDarts_vertical_eq_zero_of_not_mem
        v hvalid z hmem
    have hresidue :=
      IntegralSquareTorusCycle.residueVerticalCoeff_eq_zero_of_vertical_eq_zero
        (IntegralSquareTorusCycle.ofDarts v hvalid) p hy z hcurrent
    rw [hresidue, hcurrent, mul_zero]

theorem IntegralSquareTorusCycle.sum_dartHorizontal_eq_dirExponentX
    {L : Nat} [NeZero L] (d : ons_Dart L) :
    (∑ z : ZMod L × ZMod L,
      IntegralSquareTorusCycle.dartHorizontal d z) =
      ons_dirExponentX d.2 := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [IntegralSquareTorusCycle.dartHorizontal,
      IntegralSquareTorusCycle.pointMass, ons_dirExponentX]

theorem IntegralSquareTorusCycle.sum_dartVertical_eq_dirExponentY
    {L : Nat} [NeZero L] (d : ons_Dart L) :
    (∑ z : ZMod L × ZMod L,
      IntegralSquareTorusCycle.dartVertical d z) =
      ons_dirExponentY d.2 := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [IntegralSquareTorusCycle.dartVertical,
      IntegralSquareTorusCycle.pointMass, ons_dirExponentY]

theorem IntegralSquareTorusCycle.sum_ofDarts_horizontal_eq_dirExponentX
    {L n : Nat} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    (∑ z, (IntegralSquareTorusCycle.ofDarts v hvalid).horizontal z) =
      ∑ k, ons_dirExponentX (v k).2 := by
  change (∑ z, ∑ k, IntegralSquareTorusCycle.dartHorizontal (v k) z) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact IntegralSquareTorusCycle.sum_dartHorizontal_eq_dirExponentX (v k)

theorem IntegralSquareTorusCycle.sum_ofDarts_vertical_eq_dirExponentY
    {L n : Nat} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    (∑ z, (IntegralSquareTorusCycle.ofDarts v hvalid).vertical z) =
      ∑ k, ons_dirExponentY (v k).2 := by
  change (∑ z, ∑ k, IntegralSquareTorusCycle.dartVertical (v k) z) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact IntegralSquareTorusCycle.sum_dartVertical_eq_dirExponentY (v k)


theorem ons_simpleLoop_displacement_eq_zero_of_common_flux_divisor
    {L n p : Nat} [Fact (2 < L)] [NeZero n] [Fact (1 < p)]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (hx : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1))
    (hy : (p : Int) ∣
      (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1)) :
    (∑ k, ons_dirExponentX (v k).2) = 0 ∧
      (∑ k, ons_dirExponentY (v k).2) = 0 := by
  let C := IntegralSquareTorusCycle.ofDarts v hvalid
  let c := ons_residueLoopCoeff C p v 0
  have hconstLift :=
    ons_residueLoopCoeff_constant v hvalid hsite hnu hx hy
  have hconst : ∀ k,
      ons_residueOutgoingCoeff C p (v k).1 (v k).2 = c := by
    intro k
    have h := hconstLift (-k)
    simpa [C, c, ons_residueLoopCoeff, ons_liftSite, ons_liftDir] using h
  have hc : c ≠ 0 := by
    exact ons_residueLoopCoeff_zero_ne v hvalid hsite hnu hx hy
  constructor
  · have hsum := C.sum_residueHorizontalCoeff_eq_zero p
    have hpoint : ∀ z, C.residueHorizontalCoeff p z =
        c * C.horizontal z := by
      intro z
      exact IntegralSquareTorusCycle.residueHorizontalCoeff_eq_mul_horizontal_of_loop
        v hvalid hsite hnu hx c hconst z
    simp_rw [hpoint] at hsum
    rw [← Finset.mul_sum,
      IntegralSquareTorusCycle.sum_ofDarts_horizontal_eq_dirExponentX] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left hc
  · have hsum := C.sum_residueVerticalCoeff_eq_zero p
    have hpoint : ∀ z, C.residueVerticalCoeff p z =
        c * C.vertical z := by
      intro z
      exact IntegralSquareTorusCycle.residueVerticalCoeff_eq_mul_vertical_of_loop
        v hvalid hsite hnu hy c hconst z
    simp_rw [hpoint] at hsum
    rw [← Finset.mul_sum,
      IntegralSquareTorusCycle.sum_ofDarts_vertical_eq_dirExponentY] at hsum
    exact (mul_eq_zero.mp hsum).resolve_left hc


theorem ons_simpleLoop_winding_primitive
    {L n : Nat} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
    (mx my : Int)
    (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : Int) * mx)
    (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : Int) * my)
    (hnonzero : (mx, my) ≠ (0, 0)) :
    ∃ a b : Int, a * mx + b * my = 1 := by
  let C := IntegralSquareTorusCycle.ofDarts v hvalid
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
      (Fact.out : 2 < L)))
  have hxwrap : mx = ∑ k, ons_xWrapSign (v k) := by
    apply mul_left_cancel₀ hL
    exact hmx.symm.trans (ons_sum_dirExponentX_eq_wrap v hvalid)
  have hywrap : my = ∑ k, ons_yWrapSign (v k) := by
    apply mul_left_cancel₀ hL
    exact hmy.symm.trans (ons_sum_dirExponentY_eq_wrap v hvalid)
  have hCx : C.xFlux (-1) = mx := by
    change (IntegralSquareTorusCycle.ofDarts v hvalid).xFlux (-1) = mx
    rw [IntegralSquareTorusCycle.ofDarts_xFlux, ← hxwrap]
  have hCy : C.yFlux (-1) = my := by
    change (IntegralSquareTorusCycle.ofDarts v hvalid).yFlux (-1) = my
    rw [IntegralSquareTorusCycle.ofDarts_yFlux, ← hywrap]
  let g := Int.gcd mx my
  have hcomponent : mx ≠ 0 ∨ my ≠ 0 := by
    by_cases hx0 : mx = 0
    · right
      intro hy0
      exact hnonzero (by simp [hx0, hy0])
    · exact Or.inl hx0
  have hgpos : 0 < g := by
    rcases hcomponent with hx0 | hy0
    · exact Int.gcd_pos_of_ne_zero_left my hx0
    · exact Int.gcd_pos_of_ne_zero_right mx hy0
  have hgcd : g = 1 := by
    by_contra hg1
    have hglt : 1 < g := by omega
    letI : Fact (1 < g) := ⟨hglt⟩
    have hgx : (g : Int) ∣ C.xFlux (-1) := by
      rw [hCx]
      exact Int.gcd_dvd_left mx my
    have hgy : (g : Int) ∣ C.yFlux (-1) := by
      rw [hCy]
      exact Int.gcd_dvd_right mx my
    have hzero :=
      ons_simpleLoop_displacement_eq_zero_of_common_flux_divisor
        v hvalid hsite hnu hgx hgy
    have hmx0 : mx = 0 := by
      have : (L : Int) * mx = 0 := hmx ▸ hzero.1
      exact (mul_eq_zero.mp this).resolve_left hL
    have hmy0 : my = 0 := by
      have : (L : Int) * my = 0 := hmy ▸ hzero.2
      exact (mul_eq_zero.mp this).resolve_left hL
    exact hnonzero (by simp [hmx0, hmy0])
  refine ⟨Int.gcdA mx my, Int.gcdB mx my, ?_⟩
  change Int.gcd mx my = 1 at hgcd
  have hbezout := Int.gcd_eq_gcd_ab mx my
  rw [hgcd] at hbezout
  simpa [mul_comm] using hbezout.symm

end
end StatMech.Onsager
