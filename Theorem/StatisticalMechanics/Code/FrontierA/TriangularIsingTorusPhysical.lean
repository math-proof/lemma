/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusShiftedAssembly
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorSandwich.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
open scoped BigOperators
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangular_spinPhase_spaceRoot_mul_cos
    (L m n : Nat) [NeZero L] (a b : Fin 2) :
    (ons_spinPhase L a * ons_spaceRoot L ^ m) *
          (ons_spinPhase L b * ons_spaceRoot L ^ n) +
        ((ons_spinPhase L a * ons_spaceRoot L ^ m) *
          (ons_spinPhase L b * ons_spaceRoot L ^ n))⁻¹ =
      2 * (Real.cos
        (2 * Real.pi *
          ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L) :
        Complex) := by
  rw [ons_spinPhase_mul_spaceRoot_pow,
    ons_spinPhase_mul_spaceRoot_pow, ← Complex.exp_add]
  have hinv :
      (Complex.exp (Complex.I *
        ((2 * Real.pi *
          ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L :
            Real) : Complex)))⁻¹ =
        Complex.exp (-(Complex.I *
          ((2 * Real.pi *
            ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L :
              Real) : Complex))) :=
    (Complex.exp_neg _).symm
  rw [show Complex.I *
        ((2 * Real.pi * (m + (a.val : Real) / 2) / L : Real) : Complex) +
      Complex.I *
        ((2 * Real.pi * (n + (b.val : Real) / 2) / L : Real) : Complex) =
      Complex.I *
        ((2 * Real.pi *
          ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L :
            Real) : Complex) by push_cast; ring]
  rw [hinv, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> ring


theorem triangularTorus_sector_tanh_sq_eq_highTempProduct
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I) :
    triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingHighTempSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  letI : NeZero L :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt (Fact.out : 2 < L))⟩
  rw [triangularTorus_sector_sq_eq_det L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) rho a b hrho]
  rw [triangularTorusKWMatrix_det L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) rho
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    hrho (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos,
    triangular_spinPhase_spaceRoot_mul_cos]
  norm_cast
  unfold triangularIsingHighTempSymbol
  ring


theorem triangularTorus_normalizedSector_sq_eq_symbolProduct
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I) :
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) *
        triangularTorusWeightedSpinCharacterSum L
          (triangularTorusEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b) ^ 2 =
      ∏ j : ZMod L × ZMod L,
        (triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
  let C : Real := Real.cosh J1 * Real.cosh J2 * Real.cosh J3
  let W : Complex := triangularTorusWeightedSpinCharacterSum L
    (triangularTorusEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b
  have hW := triangularTorus_sector_tanh_sq_eq_highTempProduct
    L J1 J2 J3 rho a b hrho
  have hfactor (j : ZMod L × ZMod L) :
      (triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) =
        (C ^ 2 : Real) *
          triangularIsingHighTempSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
    have hnorm := triangularIsingHighTempSymbol_mul_cosh_sq J1 J2 J3
      (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
      (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)
    have hreal :
        triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) =
          C ^ 2 * triangularIsingHighTempSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) := by
      rw [← hnorm]
      dsimp only [C]
      ring
    exact_mod_cast hreal
  change ((((C ^ (L * L) : Real) : Complex) * W) ^ 2) = _
  rw [mul_pow, hW]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card]
  push_cast
  have hpow : ((C : Complex) ^ (L * L)) ^ 2 =
      ((C : Complex) ^ 2) ^ (L * L) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow]


theorem triangularTorus_normalizedSector_log_norm_eq
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Real.log ‖
        (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
          Complex) *
          triangularTorusWeightedSpinCharacterSum L
            (triangularTorusEdgeWeight L
              (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b‖ =
      (1 / 2 : Real) *
        ∑ j : ZMod L × ZMod L,
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) := by
  let N : Complex :=
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
      Complex) *
      triangularTorusWeightedSpinCharacterSum L
        (triangularTorusEdgeWeight L
          (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b
  let factor : ZMod L × ZMod L -> Real := fun j =>
    triangularIsingSymbol J1 J2 J3
      (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
      (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)
  have hfactor (j : ZMod L × ZMod L) : 0 < factor j := hpos _ _
  have hsq : N ^ 2 = ((∏ j, factor j : Real) : Complex) := by
    rw [show (((∏ j, factor j : Real) : Real) : Complex) =
        ∏ j, (factor j : Complex) by push_cast; rfl]
    dsimp only [N, factor]
    exact triangularTorus_normalizedSector_sq_eq_symbolProduct
      L J1 J2 J3 rho a b hrho
  have hprod : 0 < ∏ j, factor j := Finset.prod_pos fun j _ => hfactor j
  have hnormsq : ‖N‖ ^ 2 = ∏ j, factor j := by
    calc
      ‖N‖ ^ 2 = ‖N ^ 2‖ := (norm_pow N 2).symm
      _ = ‖(((∏ j, factor j : Real) : Complex))‖ := congrArg norm hsq
      _ = ∏ j, factor j := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hprod]
  have hlog := congrArg Real.log hnormsq
  rw [Real.log_pow] at hlog
  have hlogprod : Real.log (∏ j, factor j) =
      ∑ j, Real.log (factor j) := by
    exact Real.log_prod fun j _ => (hfactor j).ne'
  rw [hlogprod] at hlog
  norm_num at hlog
  change Real.log ‖N‖ = _
  calc
    Real.log ‖N‖ = (1 / 2 : Real) * (2 * Real.log ‖N‖) := by ring
    _ = (1 / 2 : Real) * ∑ j, Real.log (factor j) := by rw [hlog]
    _ = _ := by rfl

theorem triangularTorus_normalizedSector_ne_zero
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 : Real) (rho : Complex) (a b : Fin 2)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) :
        Complex) *
        triangularTorusWeightedSpinCharacterSum L
          (triangularTorusEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b ≠ 0 := by
  intro hzero
  have hsq := triangularTorus_normalizedSector_sq_eq_symbolProduct
    L J1 J2 J3 rho a b hrho
  rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hsq
  have hprod :
      (∏ j : ZMod L × ZMod L,
        triangularIsingSymbol J1 J2 J3
          (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ => (hpos _ _).ne'
  exact hprod (by exact_mod_cast hsq.symm)


theorem triangularIsingSymbol_riemann_tendsto_spinShift
    (J1 J2 J3 : Real) (a b : Fin 2)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun L : Nat => (2 * Real.pi / L) ^ 2 *
        ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          Real.log (triangularIsingSymbol J1 J2 J3
            (2 * Real.pi * (i + (a.val : Real) / 2) / L)
            (2 * Real.pi * (j + (b.val : Real) / 2) / L)))
      Filter.atTop
      (nhds (∫ k1 in (-Real.pi)..Real.pi,
        ∫ k2 in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hs : (a.val : Real) / 2 ∈ Set.Icc (0 : Real) 1 := by
    fin_cases a <;> norm_num
  have ht : (b.val : Real) / 2 ∈ Set.Icc (0 : Real) 1 := by
    fin_cases b <;> norm_num
  have h := StatMech.Onsager.ons_riemann_periodic_two_shift
    (fun k1 k2 => Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))
    (continuous_log_triangularIsingSymbol_of_pos J1 J2 J3 hpos)
    (periodic_log_triangularIsingSymbol_left J1 J2 J3)
    ((a.val : Real) / 2) ((b.val : Real) / 2) hs ht
  rw [integral_log_triangularIsingSymbol_square_shift] at h
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h


end StatMech.FrontierA
