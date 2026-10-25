/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part3


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem hasDerivAt_sinc (x : Real) :
    HasDerivAt Real.sinc (sixVertexSincDerivative x) x := by
  by_cases hx : x = 0
  · simpa [sixVertexSincDerivative, hx] using hasDerivAt_sinc_zero
  · have hquot : HasDerivAt (fun y : Real => Real.sin y / y)
        ((x * Real.cos x - Real.sin x) / x ^ 2) x := by
      simpa only [one_mul, id_eq, mul_comm] using
        (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
    rw [sixVertexSincDerivative, if_neg hx]
    apply hquot.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact Real.sinc_of_ne_zero hy

theorem sixVertexOddWallisHalfProduct_sq (m : Nat) :
    sixVertexOddWallisHalfProduct m ^ 2 =
      1 / (((2 * m + 1 : Nat) : Real) * Real.Wallis.W m) := by
  induction m with
  | zero =>
      simp [sixVertexOddWallisHalfProduct, Real.Wallis.W]
  | succ m ih =>
      rw [sixVertexOddWallisHalfProduct, Finset.prod_range_succ]
      rw [show (∏ x ∈ Finset.range m,
          ((2 * x + 1 : Nat) : Real) / (2 * x + 2)) =
          sixVertexOddWallisHalfProduct m by rfl]
      rw [Real.Wallis.W_succ, mul_pow, ih]
      push_cast
      have hm1 : (0 : Real) < 2 * m + 1 := by positivity
      have hm2 : (0 : Real) < 2 * m + 2 := by positivity
      have hm3 : (0 : Real) < 2 * m + 3 := by positivity
      have hW : 0 < Real.Wallis.W m := Real.Wallis.W_pos m
      field_simp [hm1.ne', hm2.ne', hm3.ne', hW.ne']
      ring

theorem tendsto_sixVertexOddWallisReferenceProduct (s : Nat) :
    Tendsto (fun k =>
      (sixVertexFourWidth (2 * s + 1) k : Real) *
        sixVertexOddWallisHalfProduct (s + k + 1) ^ 2)
      atTop (nhds (4 / Real.pi)) := by
  let m : Nat -> Nat := fun k => s + k + 1
  have hmNat : Tendsto m atTop atTop := by
    exact (strictMono_nat_of_lt_succ (fun k => by dsimp [m]; omega)).tendsto_atTop
  have hm : Tendsto (fun k => (m k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmNat
  have hlinear : Tendsto (fun k =>
      (sixVertexFourWidth (2 * s + 1) k : Real) /
        (((2 * m k + 1 : Nat) : Real))) atTop (nhds 2) := by
    have hden : Tendsto (fun k => (2 : Real) * (m k : Real) + 1)
        atTop atTop := (hm.const_mul_atTop (by positivity)).atTop_add
          tendsto_const_nhds
    have hsmall : Tendsto (fun k =>
        ((4 : Real) * s + 2) / ((2 : Real) * (m k : Real) + 1))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
    have hratio : Tendsto (fun k => (2 : Real) +
        ((4 : Real) * s + 2) / ((2 : Real) * (m k : Real) + 1))
        atTop (nhds 2) := by
      convert tendsto_const_nhds.add hsmall using 1 <;> norm_num
    convert hratio using 1
    · funext k
      dsimp [m]
      unfold sixVertexFourWidth
      push_cast
      field_simp
      ring
  have hW : Tendsto (fun k => Real.Wallis.W (m k)) atTop
      (nhds (Real.pi / 2)) :=
    Real.Wallis.tendsto_W_nhds_pi_div_two.comp hmNat
  have hinv : Tendsto (fun k => (Real.Wallis.W (m k))⁻¹) atTop
      (nhds ((Real.pi / 2)⁻¹)) := hW.inv₀ (by positivity)
  have hmul := hlinear.mul hinv
  have hvalue : (2 : Real) * (Real.pi / 2)⁻¹ = 4 / Real.pi := by
    field_simp [Real.pi_ne_zero]
    norm_num
  have hmul' : Tendsto (fun k =>
      (sixVertexFourWidth (2 * s + 1) k : Real) /
          (((2 * m k + 1 : Nat) : Real)) *
        (Real.Wallis.W (m k))⁻¹) atTop (nhds (4 / Real.pi)) := by
    rw [<- hvalue]
    exact hmul
  apply hmul'.congr'
  filter_upwards [] with k
  dsimp [m]
  rw [sixVertexOddWallisHalfProduct_sq]
  field_simp [Real.Wallis.W_pos (s + k + 1) |>.ne']

theorem sixVertexCanonicalOddZeroPrefactor_eq_finiteDensity
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
    sixVertexZeroPhaseBethePrefactor c
        (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
        (sixVertexOddCentralIndex (s + k + 1)) =
      c ^ 2 * (sixVertexFourWidth (2 * s + 1) k : Real) *
        (2 * Real.pi) *
          sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
            (((s + k + 1) + 1) + (s + k + 1))
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) 0 := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := ((s + k + 1) + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  have hzero :=
    sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
      hc s k hfixed
  rw [sixVertexZeroPhaseBethePrefactor_eq hc N q
    (sixVertexOddCentralIndex (s + k + 1)) hzero]
  unfold sixVertexFiniteRootDensity sixVertexThetaLeftDerivAtZero
  dsimp [N, n, q]
  have hN' : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  field_simp [hN', Real.pi_ne_zero]

theorem tendsto_sixVertexCanonicalOddFiniteDensity_zero
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) 0)
      atTop (nhds (sixVertexFourierPhysicalDensity c hc 0)) := by
  let w := sixVertexRootDensityWeight c 0
  let E := sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1)
    (sixVertexCanonicalFixedOddDensityFloor hc s)
  have hw : 0 < w := sixVertexRootDensityWeight_pos hc 0
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hmajor : Tendsto (fun k => (E / w) /
      (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityGauge_le_invWidth hc s]
      with k hk
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := ((s + k + 1) + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  have hN : 0 < (N : Real) := by
    exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
  have hpoint := (abs_weightedFiniteDensity_sub_le_gauge hc q
    (sixVertexFourierPhysicalDensityMap hc) 0
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).trans hk
  have hdiv := abs_sub_le_of_weighted_abs_sub_le_invWidth
    hN hw (le_rfl : w <= sixVertexRootDensityWeight c 0) hpoint
  rw [Real.norm_eq_abs]
  simpa [w, E, N, n, q] using hdiv

theorem sixVertexCanonicalOddLeftHalfRoot_countingFunction
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexBetheCountingFunction c
        (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k))
        (sixVertexCanonicalOddLeftHalfRoot hc s k j) =
      ((j : Real) + 1 / 2) / sixVertexFourWidth (2 * s + 1) k := by
  let t := 2 * s + 1 + k
  let N := sixVertexFourWidth (2 * s + 1) k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let i : Fin ((t + 1) + (t + 1)) :=
    Fin.natAdd (t + 1) ⟨j.val, by dsimp [t] at j ⊢; omega⟩
  have hwidth : sixVertexFourWidth 0 t = N := by
    dsimp [t, N]
    unfold sixVertexFourWidth
    omega
  have hroot := sixVertexBetheCountingFunction_at_root
    (show 0 < N from sixVertexFourWidth_pos (2 * s + 1) k)
    (show SixVertexSatisfiesBetheEquations c N ((t + 1) + (t + 1)) p by
      rw [<- hwidth]
      exact sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t) i
  have hquantum : sixVertexCentralQuantumNumber i = (j : Real) + 1 / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    dsimp [i, t]
    push_cast
    ring
  rw [hquantum] at hroot
  simpa [t, N, p, i, sixVertexCanonicalOddLeftHalfRoot,
    sixVertexCanonicalDensityPerronPositiveHalfRoots,
    sixVertexEvenPositiveHalfProjection] using hroot

theorem sixVertexCanonicalOddRightHalfRoot_countingFunction
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexBetheCountingFunction c
        (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k))
        (sixVertexCanonicalOddRightHalfRoot hc s k j) =
      ((j : Real) + 3 / 2) / sixVertexFourWidth (2 * s + 1) k := by
  let t := 2 * s + 1 + k
  let N := sixVertexFourWidth (2 * s + 1) k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let i : Fin ((t + 1) + (t + 1)) :=
    Fin.natAdd (t + 1) ⟨j.val + 1, by dsimp [t] at j ⊢; omega⟩
  have hwidth : sixVertexFourWidth 0 t = N := by
    dsimp [t, N]
    unfold sixVertexFourWidth
    omega
  have hroot := sixVertexBetheCountingFunction_at_root
    (show 0 < N from sixVertexFourWidth_pos (2 * s + 1) k)
    (show SixVertexSatisfiesBetheEquations c N ((t + 1) + (t + 1)) p by
      rw [<- hwidth]
      exact sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t) i
  have hquantum : sixVertexCentralQuantumNumber i = (j : Real) + 3 / 2 := by
    rw [sixVertexCentralQuantumNumber_eq]
    dsimp [i, t]
    push_cast
    ring
  rw [hquantum] at hroot
  simpa [t, N, p, i, sixVertexCanonicalOddRightHalfRoot,
    sixVertexCanonicalDensityPerronPositiveHalfRoots,
    sixVertexEvenPositiveHalfProjection] using hroot

theorem abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    |sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
        ((j : Real) + 1) / N| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (sixVertexCanonicalOddRightHalfRoot hc s k j -
          sixVertexCanonicalOddLeftHalfRoot hc s k j) ^ 2 / 4 := by
  dsimp
  let a := sixVertexCanonicalOddLeftHalfRoot hc s k j
  let b := sixVertexCanonicalOddRightHalfRoot hc s k j
  have hab : a <= b := by
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [a, b, sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact (horder (by simp [Fin.lt_def])).le
  have hmid := abs_sixVertexBetheCountingFunction_midpoint_defect_le
    hc (sixVertexFourWidth_pos (2 * s + 1) k) (by
      unfold sixVertexFourWidth
      omega)
    (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) hab
  rw [sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k j,
    sixVertexCanonicalOddRightHalfRoot_countingFunction hc s k j] at hmid
  change |(((j : Real) + 1 / 2) /
          (sixVertexFourWidth (2 * s + 1) k : Real) +
        (((j : Real) + 3 / 2) /
          (sixVertexFourWidth (2 * s + 1) k : Real))) / 2 -
      sixVertexBetheCountingFunction c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k))
        ((a + b) / 2)| <= _ at hmid
  have hN : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  rw [show (((j : Real) + 1 / 2) /
          (sixVertexFourWidth (2 * s + 1) k : Real) +
        ((j : Real) + 3 / 2) /
          (sixVertexFourWidth (2 * s + 1) k : Real)) / 2 =
      ((j : Real) + 1) /
        (sixVertexFourWidth (2 * s + 1) k : Real) by
          field_simp [hN]
          ring] at hmid
  simpa [abs_sub_comm, a, b, sixVertexCanonicalOddMidpointHalfRoot]
    using hmid

theorem sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x)
    (j : Fin (s + k + 1)) :
    sixVertexCanonicalOddRightHalfRoot hc s k j -
        sixVertexCanonicalOddLeftHalfRoot hc s k j <=
      1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let rho := sixVertexFiniteRootDensity c N n p
  let a := sixVertexCanonicalOddLeftHalfRoot hc s k j
  let b := sixVertexCanonicalOddRightHalfRoot hc s k j
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hab : a <= b := by
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [a, b, sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact (horder (by simp [Fin.lt_def])).le
  have hint := intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p a b
  rw [sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k j,
    sixVertexCanonicalOddRightHalfRoot_countingFunction hc s k j] at hint
  have hmass : (∫ x in a..b, rho x) = 1 / (N : Real) := by
    rw [show (∫ x in a..b, rho x) =
        ((j : Real) + 3 / 2) / (N : Real) -
          ((j : Real) + 1 / 2) / (N : Real) by
      simpa [rho, N, n, p] using hint]
    field_simp [hNreal.ne']
    ring_nf
  have hmono := intervalIntegral.integral_mono_on hab
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N n p).intervalIntegrable _ _)
    (fun x _ => by simpa [rho, N, n, p] using hdensity x)
  rw [intervalIntegral.integral_const, hmass] at hmono
  simp only [smul_eq_mul] at hmono
  change (b - a) * lower <= 1 / (N : Real) at hmono
  rw [le_div_iff₀ (mul_pos hNreal hlower)]
  have hmul := mul_le_mul_of_nonneg_left hmono hNreal.le
  field_simp [hNreal.ne', hlower.ne'] at hmul ⊢
  nlinarith

theorem abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le_invWidthSq
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x)
    (j : Fin (s + k + 1)) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    |sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
        ((j : Real) + 1) / N| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
        (4 * ((N : Real) * lower) ^ 2) := by
  dsimp
  have hbasic :=
    abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le
      hc s k j
  have hgap := sixVertexCanonicalOddHalfRoot_gap_le_of_densityLower
    hc s k hlower hdensity j
  have hgapNonneg : 0 <= sixVertexCanonicalOddRightHalfRoot hc s k j -
      sixVertexCanonicalOddLeftHalfRoot hc s k j := by
    have hl := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val, by omega⟩
    have hr := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val + 1, by omega⟩
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact sub_nonneg.mpr (horder (by simp [Fin.lt_def])).le
  have hcoef : 0 <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) :=
    NNReal.coe_nonneg _
  calc
    _ <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (sixVertexCanonicalOddRightHalfRoot hc s k j -
          sixVertexCanonicalOddLeftHalfRoot hc s k j) ^ 2 / 4 := hbasic
    _ <= (sixVertexFiniteRootDensityLipschitzConstant c : Real) *
        (1 / ((sixVertexFourWidth (2 * s + 1) k : Real) * lower)) ^ 2 / 4 := by
      gcongr
    _ = (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
        (4 * (((sixVertexFourWidth (2 * s + 1) k : Real) * lower)) ^ 2) := by
      field_simp [(show (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 by
        exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'), hlower.ne']

theorem abs_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x)
    (j : Fin (s + k + 1)) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    |Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
        Real.log (((j : Real) + 1) / N)| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
        (2 * (N : Real) * lower ^ 2 * ((j : Real) + 1)) := by
  dsimp
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let F := sixVertexBetheCountingFunction c N n p
  let a := sixVertexCanonicalOddLeftHalfRoot hc s k j
  let b := sixVertexCanonicalOddRightHalfRoot hc s k j
  let mid := sixVertexCanonicalOddMidpointHalfRoot hc s k j
  let q : Real := ((j : Real) + 1) / (2 * N)
  let y : Real := ((j : Real) + 1) / N
  have hN : 0 < (N : Real) := by
    exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
  have hj : 0 < (j : Real) + 1 := by positivity
  have hq : 0 < q := div_pos hj (mul_pos (by norm_num) hN)
  have hab : a <= b := by
    have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).1
    dsimp [a, b, sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection]
    exact (horder (by simp [Fin.lt_def])).le
  have haMid : a <= mid := by
    dsimp [mid, sixVertexCanonicalOddMidpointHalfRoot]
    linarith
  have hFmono : Monotone F :=
    monotone_sixVertexBetheCountingFunction_of_finiteDensity_nonneg
      hc (sixVertexFourWidth_pos (2 * s + 1) k) p
        (fun x => (hlower.le.trans (hdensity x)))
  have hFa : F a = ((j : Real) + 1 / 2) / N := by
    simpa [F, N, n, p, a] using
      sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k j
  have hqFa : q <= F a := by
    rw [hFa]
    dsimp [q]
    field_simp [hN.ne']
    nlinarith [show 0 <= (j : Real) by positivity]
  have hqFmid : q <= F mid := hqFa.trans (hFmono haMid)
  have hqy : q <= y := by
    dsimp [q, y]
    field_simp [hN.ne']
    nlinarith
  have hlog := abs_log_sub_log_le_of_pos_lower hq hqFmid hqy
  have hdefect :=
    abs_sixVertexCanonicalOddMidpointHalfRoot_countingFunction_sub_le_invWidthSq
      hc s k hlower hdensity j
  change |F mid - y| <=
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
        (4 * ((N : Real) * lower) ^ 2) at hdefect
  calc
    |Real.log (F mid) - Real.log y| <= |F mid - y| / q := hlog
    _ <= ((sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          (4 * ((N : Real) * lower) ^ 2)) / q :=
      div_le_div_of_nonneg_right hdefect hq.le
    _ = (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
        (2 * (N : Real) * lower ^ 2 * ((j : Real) + 1)) := by
      dsimp [q]
      field_simp [hN.ne', hlower.ne', hj.ne']
      ring

theorem abs_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le
    {c : Real} (hc : 2 < c) (s k : Nat) {lower : Real}
    (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    |∑ j : Fin (s + k + 1),
        (Real.log (sixVertexBetheCountingFunction c N n p
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
          Real.log (((j : Real) + 1) / N))| <=
      ((sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          (2 * (N : Real) * lower ^ 2)) *
        (1 + Real.log (s + k + 1 : Nat)) := by
  dsimp
  let N := sixVertexFourWidth (2 * s + 1) k
  let A := (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
    (2 * (N : Real) * lower ^ 2)
  have hA : 0 <= A := by
    dsimp [A]
    positivity
  calc
    _ <= ∑ j : Fin (s + k + 1),
        |Real.log (sixVertexBetheCountingFunction c N
            ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
            (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k))
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
          Real.log (((j : Real) + 1) / N)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ j : Fin (s + k + 1), A / ((j : Real) + 1) := by
      apply Finset.sum_le_sum
      intro j _
      simpa [A, N, div_div] using
        abs_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le
          hc s k hlower hdensity j
    _ = A * (harmonic (s + k + 1) : Real) := by
      calc
        (∑ j : Fin (s + k + 1), A / ((j : Real) + 1)) =
            ∑ j ∈ Finset.range (s + k + 1), A / ((j : Real) + 1) :=
          by simpa using (Fin.sum_univ_eq_sum_range
            (fun j : Nat => A / ((j : Real) + 1)) (s + k + 1))
        _ = A * (harmonic (s + k + 1) : Real) := by
          simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_range] at hj
          field_simp
          push_cast
          rfl
    _ <= A * (1 + Real.log (s + k + 1 : Nat)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) hA

theorem tendsto_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k =>
      let N := sixVertexFourWidth (2 * s + 1) k
      let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
      let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      ∑ j : Fin (s + k + 1),
        (Real.log (sixVertexBetheCountingFunction c N n p
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
          Real.log (((j : Real) + 1) / N))) atTop (nhds 0) := by
  let lower := sixVertexCanonicalHalfDensityFloor hc
  let C : Real := (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
    (2 * lower ^ 2)
  have hlower : 0 < lower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hone : Tendsto (fun k => (1 : Real) /
      (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hlog : Tendsto (fun k =>
      Real.log (sixVertexFourWidth (2 * s + 1) k : Real) /
        (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hwidth
  have hmajor : Tendsto (fun k => C *
      ((1 + Real.log (sixVertexFourWidth (2 * s + 1) k : Real)) /
        (sixVertexFourWidth (2 * s + 1) k : Real))) atTop (nhds 0) := by
    convert (hone.add hlog).const_mul C using 1
    · funext k
      ring
    · ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hfloor := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  filter_upwards [hfloor] with k hk
  have hk' : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x := by
    simpa [lower, sixVertexFourWidth] using hk
  have hbound :=
    abs_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference_le
      hc s k hlower hk'
  rw [Real.norm_eq_abs, sub_zero]
  calc
    _ <= ((sixVertexFiniteRootDensityLipschitzConstant c : Real) /
          (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower ^ 2)) *
        (1 + Real.log (s + k + 1 : Nat)) := hbound
    _ = C * ((1 + Real.log (s + k + 1 : Nat)) /
        (sixVertexFourWidth (2 * s + 1) k : Real)) := by
      dsimp [C]
      ring
    _ <= C * ((1 + Real.log (sixVertexFourWidth (2 * s + 1) k : Real)) /
        (sixVertexFourWidth (2 * s + 1) k : Real)) := by
      have hC : 0 <= C := by dsimp [C]; positivity
      have hmPos : 0 < (s + k + 1 : Real) := by positivity
      have hmN : (s + k + 1 : Real) <=
          sixVertexFourWidth (2 * s + 1) k := by
        exact_mod_cast (show s + k + 1 <=
          sixVertexFourWidth (2 * s + 1) k by
            unfold sixVertexFourWidth
            omega)
      have hlogLe := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hmPos)
        (Set.mem_Ioi.mpr (show 0 < (sixVertexFourWidth (2 * s + 1) k : Real) by
          exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k)) hmN
      apply mul_le_mul_of_nonneg_left _ hC
      apply div_le_div_of_nonneg_right _
        (show 0 <= (sixVertexFourWidth (2 * s + 1) k : Real) by positivity)
      have hlogLe' : Real.log (s + k + 1 : Nat) <=
          Real.log (sixVertexFourWidth (2 * s + 1) k : Real) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hlogLe
      simpa [add_comm] using add_le_add_left hlogLe' 1

end
end StatMech.FrontierD
