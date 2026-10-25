/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Def.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part3
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

theorem isingMomentumChar_site_re
    {k : Nat} (p : IsingDyadicTorus d k) (x : Site d) :
    (conj (isingTorusMomentumChar p
      (isingSiteToDyadicTorus k x))).re =
      Real.cos (2 * Real.pi * ∑ i : Fin d,
        isingTorusCenteredMomentumFun p i * (x i : Real)) := by
  rw [Complex.conj_re, isingTorusMomentumChar_apply]
  have hterm (i : Fin d) :
      ZMod.stdAddChar (p i * isingSiteToDyadicTorus k x i) =
        Complex.exp (((2 * Real.pi *
          isingTorusCenteredMomentumFun p i * (x i : Real) : Real) :
            Complex) * Complex.I) := by
    have harg : p i * isingSiteToDyadicTorus k x i =
        (((p i).valMinAbs * x i : Int) : ZMod (2 ^ (k + 2))) := by
      unfold isingSiteToDyadicTorus
      calc
        p i * (x i : ZMod (2 ^ (k + 2))) =
            ((p i).valMinAbs : ZMod (2 ^ (k + 2))) *
              (x i : ZMod (2 ^ (k + 2))) := by
          rw [ZMod.coe_valMinAbs]
        _ = (((p i).valMinAbs * x i : Int) :
            ZMod (2 ^ (k + 2))) := (Int.cast_mul _ _).symm
    rw [harg]
    rw [ZMod.stdAddChar_coe]
    congr 1
    simp only [isingTorusCenteredMomentumFun_apply]
    push_cast
    have hside : ((isingDyadicSide k : Real) : Complex) ≠ 0 := by
      exact_mod_cast (isingDyadicSide_pos k).ne'
    field_simp [isingDyadicSide, hside]
    simp only [isingDyadicSide, pow_add]
    norm_num
  simp_rw [hterm]
  rw [← Complex.exp_sum]
  have hsum :
      ∑ i : Fin d,
          (((2 * Real.pi * isingTorusCenteredMomentumFun p i *
            (x i : Real) : Real) : Complex) * Complex.I) =
        ((2 * Real.pi * ∑ i : Fin d,
          isingTorusCenteredMomentumFun p i * (x i : Real) : Real) :
            Complex) * Complex.I := by
    rw [← Finset.sum_mul]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, Complex.exp_ofReal_mul_I_re]

theorem isingDyadicTorus_card (d k : Nat) :
    Fintype.card (IsingDyadicTorus d k) = isingDyadicSide k ^ d := by
  simp [IsingDyadicTorus, isingDyadicSide, Fintype.card_fun]


theorem isingDyadicTorusGreen_eq_character_sum
    {k : Nat} (x : Site d) :
    isingDyadicTorusGreen x k =
      (1 / Fintype.card (IsingDyadicTorus d k) : Real) *
        ∑ p : IsingDyadicTorus d k,
          if p = 0 then 0 else
            (conj (isingTorusMomentumChar p
              (isingSiteToDyadicTorus k x))).re *
            (isingTorusCharacterDispersion
              (isingTorusMomentumChar p))⁻¹ := by
  unfold isingDyadicTorusGreen
  rw [isingDyadicTorus_card, Nat.cast_pow]
  simp_rw [isingMomentumChar_site_re]
  ring

theorem isingNormalizedCoordinateDispersion_zero :
    isingNormalizedCoordinateDispersion
      (0 : IsingMomentumCoordinates d) = 0 := by
  simp [isingNormalizedCoordinateDispersion]


theorem isingDyadicTorusGreen_sub_regularized_abs_le
    {k M : Nat} (eta : Real) (heta : 0 < eta) (x : Fin d → Int)
    (hsmall : ∀ p : IsingDyadicTorus d k, p ≠ 0 →
      isingTorusCharacterDispersion (isingTorusMomentumChar p) < eta →
      p ∈ isingTorusLowMomentum d k M) :
    |isingDyadicTorusGreen x k -
        isingRegularizedTorusGreen eta x k| ≤
      (1 / (isingDyadicSide k : Real) ^ d) *
        (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
          (isingTorusCharacterDispersion
            (isingTorusMomentumChar p))⁻¹) := by
  classical
  let D : IsingDyadicTorus d k → Real := fun p =>
    isingTorusCharacterDispersion (isingTorusMomentumChar p)
  let phase : IsingDyadicTorus d k → Real := fun p =>
    Real.cos (2 * Real.pi * ∑ i : Fin d,
      isingTorusCenteredMomentumFun p i * (x i : Real))
  have hDpos (p : IsingDyadicTorus d k) (hp : p ≠ 0) : 0 < D p :=
    isingTorusCharacterDispersion_pos_of_ne_zero
      (isingTorusMomentumChar p)
      (by
        intro hzero
        exact hp ((isingTorusMomentumChar_eq_zero_iff p).mp hzero))
  have hpoint (p : IsingDyadicTorus d k) :
      |(if p = 0 then 0 else phase p * (D p)⁻¹) -
          phase p * (max (D p) eta)⁻¹| ≤
        if p = 0 then eta⁻¹ else
          if p ∈ isingTorusLowMomentum d k M then (D p)⁻¹ else 0 := by
    by_cases hp0 : p = 0
    · subst p
      have hcenter : isingTorusCenteredMomentumFun
          (0 : IsingDyadicTorus d k) = 0 := by
        funext i
        simp
      have hD0 : D (0 : IsingDyadicTorus d k) = 0 := by
        dsimp [D]
        rw [← isingNormalizedCoordinateDispersion_centered]
        rw [hcenter, isingNormalizedCoordinateDispersion_zero]
      simp only [if_true, hD0, max_eq_right heta.le]
      have hphase0 : phase (0 : IsingDyadicTorus d k) = 1 := by
        simp [phase, hcenter]
      rw [hphase0, one_mul, zero_sub, abs_neg,
        abs_of_pos (inv_pos.mpr heta)]
    · simp only [hp0, if_false]
      by_cases hlow : p ∈ isingTorusLowMomentum d k M
      · simp only [hlow, if_true]
        have hDp := hDpos p hp0
        have hmax : 0 < max (D p) eta :=
          lt_of_lt_of_le hDp (le_max_left _ _)
        have hinv : (max (D p) eta)⁻¹ ≤ (D p)⁻¹ :=
          (inv_le_inv₀ hmax hDp).2 (le_max_left _ _)
        rw [← mul_sub]
        calc
          |phase p * ((D p)⁻¹ - (max (D p) eta)⁻¹)| =
              |phase p| * ((D p)⁻¹ - (max (D p) eta)⁻¹) := by
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hinv)]
          _ ≤ 1 * ((D p)⁻¹ - (max (D p) eta)⁻¹) := by
            gcongr
            exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
          _ ≤ (D p)⁻¹ := by
            have : 0 ≤ (max (D p) eta)⁻¹ := inv_nonneg.mpr hmax.le
            linarith
      · simp only [hlow, if_false]
        have hnotSmall : eta ≤ D p := by
          by_contra hlt
          exact hlow (hsmall p hp0 (lt_of_not_ge hlt))
        rw [max_eq_left hnotSmall, sub_self, abs_zero]
  have hsum :
      |∑ p : IsingDyadicTorus d k,
          ((if p = 0 then 0 else phase p * (D p)⁻¹) -
            phase p * (max (D p) eta)⁻¹)| ≤
        eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, (D p)⁻¹ := by
    calc
      |∑ p : IsingDyadicTorus d k,
          ((if p = 0 then 0 else phase p * (D p)⁻¹) -
            phase p * (max (D p) eta)⁻¹)| ≤
          ∑ p : IsingDyadicTorus d k,
            |(if p = 0 then 0 else phase p * (D p)⁻¹) -
              phase p * (max (D p) eta)⁻¹| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : IsingDyadicTorus d k,
          (if p = 0 then eta⁻¹ else
            if p ∈ isingTorusLowMomentum d k M then (D p)⁻¹ else 0) :=
        Finset.sum_le_sum fun p _ => hpoint p
      _ = eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, (D p)⁻¹ := by
        let f : IsingDyadicTorus d k → Real := fun p =>
          if p = 0 then eta⁻¹ else
            if p ∈ isingTorusLowMomentum d k M then (D p)⁻¹ else 0
        calc
          ∑ p : IsingDyadicTorus d k, f p =
              ∑ p ∈ (Finset.univ.erase
                (0 : IsingDyadicTorus d k)), f p + f 0 :=
            (Finset.sum_erase_add Finset.univ f
              (Finset.mem_univ 0)).symm
          _ = f 0 + ∑ p ∈ (Finset.univ.erase
                (0 : IsingDyadicTorus d k)), f p := by ring
          _ = eta⁻¹ + ∑ p ∈ (Finset.univ.erase
                (0 : IsingDyadicTorus d k)), f p := by
            simp [f]
          _ = eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, f p := by
            congr 1
            symm
            apply Finset.sum_subset
            · intro p hp
              rw [Finset.mem_erase]
              exact ⟨(isingTorusLowMomentum_mem_iff p).mp hp |>.1,
                Finset.mem_univ p⟩
            · intro p hpErase hpNotLow
              have hp0 := (Finset.mem_erase.mp hpErase).1
              simp [f, hp0, hpNotLow]
          _ = eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
              (D p)⁻¹ := by
            apply congrArg (eta⁻¹ + ·)
            apply Finset.sum_congr rfl
            intro p hp
            have hp0 := (isingTorusLowMomentum_mem_iff p).mp hp |>.1
            simp [f, hp0, hp]
  have hsideBase : (0 : Real) < isingDyadicSide k := by
    exact_mod_cast isingDyadicSide_pos k
  have hside : (0 : Real) < (isingDyadicSide k : Real) ^ d :=
    pow_pos hsideBase _
  unfold isingDyadicTorusGreen isingRegularizedTorusGreen
  simp only [isingRegularizedGreenIntegrand,
    isingRegularizedInverseDispersion,
    isingNormalizedCoordinateDispersion_centered]
  change |(∑ p, if p = 0 then 0 else phase p * (D p)⁻¹) /
      (isingDyadicSide k : Real) ^ d -
    (∑ p, phase p * (max (D p) eta)⁻¹) /
      (isingDyadicSide k : Real) ^ d| ≤ _
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div,
    abs_of_pos hside]
  calc
    |∑ p, ((if p = 0 then 0 else phase p * (D p)⁻¹) -
        phase p * (max (D p) eta)⁻¹)| /
        (isingDyadicSide k : Real) ^ d ≤
      (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, (D p)⁻¹) /
        (isingDyadicSide k : Real) ^ d :=
      div_le_div_of_nonneg_right hsum hside.le
    _ = (1 / (isingDyadicSide k : Real) ^ d) *
        (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
          (isingTorusCharacterDispersion
            (isingTorusMomentumChar p))⁻¹) := by
      dsimp [D]
      ring


theorem isingTorus_smallDispersion_mem_lowMomentum
    {k : Nat} (delta eta : Real) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2) (heta : eta ≤ 16 * delta ^ 2)
    (p : IsingDyadicTorus d k) (hp0 : p ≠ 0)
    (hpeta : isingTorusCharacterDispersion
      (isingTorusMomentumChar p) < eta) :
    p ∈ isingTorusLowMomentum d k
      ⌈delta * isingDyadicSide k⌉₊ := by
  let L : Real := isingDyadicSide k
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast isingDyadicSide_pos k
  have hpFull : p ∈ isingTorusLowMomentum d k
      (isingDyadicSide k / 2) := by
    rw [isingTorusLowMomentum_mem_iff]
    exact ⟨hp0, fun i => ZMod.natAbs_valMinAbs_le (p i)⟩
  have hlower := isingTorusCharacterDispersion_centered_lower
    hpFull (le_refl (isingDyadicSide k / 2))
  rw [isingTorusLowMomentum_mem_iff]
  refine ⟨hp0, ?_⟩
  intro i
  let z : Real := ((p i).valMinAbs : Real)
  have hzSqLe : z ^ 2 ≤
      integerMomentumNormSq (isingTorusCenteredIntMomentum p) := by
    unfold integerMomentumNormSq
    dsimp [z, isingTorusCenteredIntMomentum]
    exact Finset.single_le_sum (s := Finset.univ)
      (fun j _ => sq_nonneg (((p j).valMinAbs : Int) : Real))
      (Finset.mem_univ i)
  have hzLower : (16 / L ^ 2) * z ^ 2 ≤
      isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
    calc
      (16 / L ^ 2) * z ^ 2 ≤
          (16 / L ^ 2) *
            integerMomentumNormSq (isingTorusCenteredIntMomentum p) := by
        gcongr
      _ ≤ isingTorusCharacterDispersion (isingTorusMomentumChar p) :=
        hlower
  have hzScaled :
      ((16 / L ^ 2) * z ^ 2) * L ^ 2 <
        (16 * delta ^ 2) * L ^ 2 := by
    apply mul_lt_mul_of_pos_right _ (sq_pos_of_pos hL)
    exact lt_of_le_of_lt hzLower (hpeta.trans_le heta)
  have hzSq : z ^ 2 < (delta * L) ^ 2 := by
    field_simp [hL.ne'] at hzScaled
    nlinarith
  have hzAbs : |z| < delta * L := by
    rw [sq_lt_sq] at hzSq
    simpa [abs_of_pos (mul_pos hdelta hL)] using hzSq
  have hnatAbsCast : (((p i).valMinAbs.natAbs : Nat) : Real) = |z| := by
    dsimp [z]
    generalize (p i).valMinAbs = a
    cases a with
    | ofNat n => simp
    | negSucc n =>
        simp only [Int.cast_negSucc, Int.natAbs_negSucc,
          Nat.cast_add, Nat.cast_one]
        have hn : -((n : Real) + 1) ≤ 0 := neg_nonpos.mpr (by positivity)
        rw [abs_of_nonpos hn]
        norm_cast
  have hceil := Nat.le_ceil (delta * L)
  exact_mod_cast (show (((p i).valMinAbs.natAbs : Nat) : Real) ≤
      (⌈delta * L⌉₊ : Nat) by
    rw [hnatAbsCast]
    exact hzAbs.le.trans hceil)

theorem isingLowMomentumRadius_le_half
    {k : Nat} (delta : Real) (hdelta : 0 ≤ delta)
    (hdeltaHalf : delta ≤ 1 / 2) :
    ⌈delta * isingDyadicSide k⌉₊ ≤ isingDyadicSide k / 2 := by
  rw [Nat.ceil_le]
  have hsideEven : 2 ∣ isingDyadicSide k := by
    simp [isingDyadicSide]
  have hcast : ((isingDyadicSide k / 2 : Nat) : Real) =
      (isingDyadicSide k : Real) / 2 := by
    rw [Nat.cast_div hsideEven (by norm_num)]
    norm_num
  rw [hcast]
  have hside : (0 : Real) ≤ isingDyadicSide k := by positivity
  nlinarith

theorem isingRegularizedTorusGreen_eq_grid
    (eta : Real) (x : Fin d → Int) (k : Nat) :
    isingRegularizedTorusGreen eta x k =
      isingRegularizedGridGreen eta x (isingDyadicSide k) := by
  unfold isingRegularizedTorusGreen isingRegularizedGridGreen
  rw [← (isingTorusMomentumGridEquiv d k).tsum_eq
    (fun q => isingRegularizedGreenIntegrand eta x q)]
  simp only [isingTorusMomentumGridEquiv_apply, tsum_fintype,
    Nat.cast_pow]

theorem measurableSet_isingNormalizedCoordinateCube (d : Nat) :
    MeasurableSet (isingNormalizedCoordinateCube d) := by
  unfold isingNormalizedCoordinateCube
  rw [show {q : IsingMomentumCoordinates d |
      ∀ i, (-1 / 2 : Real) < q i ∧ q i ≤ 1 / 2} =
      ⋂ i : Fin d, ({q | (-1 / 2 : Real) < q i} ∩
        {q | q i ≤ 1 / 2}) by ext q; simp]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (measurable_pi_apply i) measurable_const)

theorem isBounded_isingNormalizedCoordinateCube (d : Nat) :
    IsBounded (isingNormalizedCoordinateCube d) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  intro q hq
  rw [Pi.norm_def]
  rw [← NNReal.coe_one, NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm,
    Real.norm_eq_abs]
  have hi := hq i
  exact (abs_le.mpr ⟨by linarith, hi.2⟩).trans (by norm_num)

theorem ordConnected_isingNormalizedCoordinateCube (d : Nat) :
    (isingNormalizedCoordinateCube d).OrdConnected := by
  constructor
  intro x hx y hy z hz i
  exact ⟨lt_of_lt_of_le (hx i).1 (hz.1 i),
    le_trans (hz.2 i) (hy i).2⟩

theorem volume_frontier_isingNormalizedCoordinateCube (d : Nat) :
    volume (frontier (isingNormalizedCoordinateCube d)) = 0 :=
  (ordConnected_isingNormalizedCoordinateCube d).null_frontier

theorem continuous_isingNormalizedCoordinateDispersion (d : Nat) :
    Continuous (isingNormalizedCoordinateDispersion :
      IsingMomentumCoordinates d → Real) := by
  unfold isingNormalizedCoordinateDispersion
  fun_prop

theorem continuous_isingRegularizedInverseDispersion
    (eta : Real) (heta : 0 < eta) :
    Continuous (isingRegularizedInverseDispersion eta :
      IsingMomentumCoordinates d → Real) := by
  unfold isingRegularizedInverseDispersion
  apply Continuous.inv₀
  · exact (continuous_isingNormalizedCoordinateDispersion d).max continuous_const
  · intro q
    exact (lt_of_lt_of_le heta (le_max_right _ _)).ne'

theorem continuous_isingRegularizedGreenIntegrand
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Continuous (isingRegularizedGreenIntegrand eta x :
      IsingMomentumCoordinates d → Real) := by
  unfold isingRegularizedGreenIntegrand
  apply Continuous.mul
  · fun_prop
  · exact continuous_isingRegularizedInverseDispersion eta heta


end StatMech.FrontierA
