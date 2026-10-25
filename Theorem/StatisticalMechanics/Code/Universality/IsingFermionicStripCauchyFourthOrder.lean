/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSpatialResidualComparison.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality.Part4
open Metric


noncomputable section

set_option maxHeartbeats 1800000 in

theorem isingFermionic_verticalOscillation_cauchy_fourth
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d ->
      |(Phi z).im - (Phi c).im| <= C) :
    ‖iteratedDeriv 4 Phi c‖ <= 768 * C / d ^ 4 := by
  let shift : Complex -> Complex := fun t => Phi (c + t)
  have hmap : Set.MapsTo (fun t : Complex => c + t) (ball 0 d) (ball c d) := by
    intro t ht
    simpa [Metric.mem_ball, dist_eq_norm] using ht
  have hshift : DifferentiableOn Complex shift (ball 0 d) := by
    exact hPhi.comp ((differentiableOn_const c).add differentiableOn_id) hmap
  let g : Complex -> Complex := fun t => -Complex.I * (shift t - shift 0)
  have hg : DifferentiableOn Complex g (ball 0 d) := by
    exact (differentiableOn_const (-Complex.I)).mul
      (hshift.sub (differentiableOn_const (shift 0)))
  have hgre : Set.MapsTo g (ball 0 d) {z | z.re <= C} := by
    intro t ht
    have htOsc := hosc (c + t) (hmap ht)
    change (-Complex.I * (shift t - shift 0)).re <= C
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero,
      zero_mul, Complex.neg_im, Complex.I_im, neg_one_mul, zero_sub,
      Complex.sub_im, shift]
    simpa using (le_of_abs_le htOsc)
  have hgzero : g 0 = 0 := by simp [g]
  have hB : forall t, t ∈ sphere 0 (d / 2) ->
      ‖shift t - shift 0‖ <= 2 * C := by
    intro t ht
    have hnorm : ‖t‖ = d / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ht
    have htball : t ∈ ball 0 d := by
      simp only [_root_.Metric.mem_ball, dist_eq_norm, sub_zero, hnorm]
      linarith
    have hb := Complex.borelCaratheodory_zero
      (f := g) (R := d) (M := C) (z := t)
      hC hg hgre hd htball hgzero
    have hgnorm : ‖g t‖ = ‖shift t - shift 0‖ := by
      simp [g]
    rw [hgnorm, hnorm] at hb
    calc
      ‖shift t - shift 0‖ <= 2 * C * (d / 2) / (d - d / 2) := hb
      _ = 2 * C := by
        field_simp [hd.ne']
        ring
  have hgSmall : DiffContOnCl Complex g (ball 0 (d / 2)) := by
    constructor
    · exact hg.mono (Metric.ball_subset_ball (by linarith))
    · apply hg.continuousOn.mono
      rw [closure_ball 0 (by positivity)]
      exact Metric.closedBall_subset_ball (by linarith)
  have hBg : forall t, t ∈ sphere 0 (d / 2) -> ‖g t‖ <= 2 * C := by
    intro t ht
    have hgnorm : ‖g t‖ = ‖shift t - shift 0‖ := by simp [g]
    rw [hgnorm]
    exact hB t ht
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := g) 4 (by positivity : 0 < d / 2) hgSmall hBg
  have hgfun : g = fun t => Complex.I * shift 0 + (-Complex.I) * shift t := by
    funext t
    simp only [g]
    ring
  have hgderiv : iteratedDeriv 4 g 0 =
      -Complex.I * iteratedDeriv 4 shift 0 := by
    rw [hgfun, iteratedDeriv_const_add (by norm_num)]
    exact iteratedDeriv_const_mul_field (-Complex.I) shift
  have hnormderiv : ‖iteratedDeriv 4 g 0‖ =
      ‖iteratedDeriv 4 shift 0‖ := by
    rw [hgderiv]
    simp
  rw [hnormderiv, iteratedDeriv_comp_const_add 4 Phi c] at hc
  dsimp [shift] at hc
  have hscale : (Nat.factorial 4 : Real) * (2 * C) / (d / 2) ^ 4 =
      768 * C / d ^ 4 := by
    norm_num
    field_simp [hd.ne']
    ring
  rw [hscale] at hc
  simpa using hc


theorem isingFermionic_strip_cauchy_fourth
    (Phi : Complex -> Complex) (c : Complex) (d : Real)
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall z, z ∈ ball c d ->
      0 <= (Phi z).im /\ (Phi z).im <= 1) :
    ‖iteratedDeriv 4 Phi c‖ <= 768 / d ^ 4 := by
  have hosc : forall z, z ∈ ball c d ->
      |(Phi z).im - (Phi c).im| <= 1 := by
    intro z hz
    have hzRange := hrange z hz
    have hcRange := hrange c (Metric.mem_ball_self hd)
    rw [abs_le]
    constructor <;> linarith
  simpa using isingFermionic_verticalOscillation_cauchy_fourth
    Phi c d 1 hd one_pos hPhi hosc


theorem isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv
    (Phi : Complex -> Complex) (c : Complex)
    (hPhi : ContDiffAt Complex 4 Phi c) :
    ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <=
      ‖iteratedDeriv 4 Phi c‖ := by
  have hreal : ContDiffAt Real 4 Phi c := hPhi.restrict_scalars Real
  have him := Complex.imCLM.norm_iteratedFDeriv_comp_left
    (n := 4) (N := 4) hreal (by norm_num)
  rw [Complex.imCLM_norm, one_mul] at him
  change ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <= _ at him
  rw [← hPhi.restrictScalars_iteratedFDeriv (𝕜 := Real)] at him
  simp only [Function.comp_apply] at him
  rw [ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] at him
  exact him


theorem isingFermionic_verticalOscillation_im_fourth_tensor
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d ->
      |(Phi z).im - (Phi c).im| <= C) :
    ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <=
      768 * C / d ^ 4 := by
  have hPhiAt : ContDiffAt Complex 4 Phi c :=
    (hPhi.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hd))
  exact (isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv
    Phi c hPhiAt).trans
    (isingFermionic_verticalOscillation_cauchy_fourth
      Phi c d C hd hC hPhi hosc)


theorem isingFermionic_strip_im_fourth_tensor
    (Phi : Complex -> Complex) (c : Complex) (d : Real)
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall z, z ∈ ball c d ->
      0 <= (Phi z).im /\ (Phi z).im <= 1) :
    ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) c‖ <=
      768 / d ^ 4 := by
  have hPhiAt : ContDiffAt Complex 4 Phi c :=
    (hPhi.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hd))
  exact (isingFermionic_norm_iteratedFDeriv_real_im_le_iteratedDeriv
    Phi c hPhiAt).trans
    (isingFermionic_strip_cauchy_fourth Phi c d hd hPhi hrange)

theorem isingFermionic_ball_half_subset_ball_of_mem
    {c w : Complex} {d : Real} (hw : w ∈ ball c (d / 2)) :
    ball w (d / 2) ⊆ ball c d := by
  intro z hz
  rw [Metric.mem_ball] at hw hz ⊢
  calc
    dist z c <= dist z w + dist w c := dist_triangle _ _ _
    _ < d / 2 + d / 2 := add_lt_add hz hw
    _ = d := by ring


theorem isingFermionic_verticalOscillation_im_fourthTensor_le_on_halfBall
    (Phi : Complex -> Complex) (c : Complex) (d C : Real)
    (hd : 0 < d) (hC : 0 < C)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hosc : forall z, z ∈ ball c d -> forall w, w ∈ ball c d ->
      |(Phi z).im - (Phi w).im| <= C) :
    forall w, w ∈ ball c (d / 2) ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <=
        12288 * C / d ^ 4 := by
  intro w hw
  have hsub := isingFermionic_ball_half_subset_ball_of_mem hw
  have hlocal := isingFermionic_verticalOscillation_im_fourth_tensor
    Phi w (d / 2) C (by positivity) hC (hPhi.mono hsub)
      (fun z hz => hosc z (hsub hz) w (hsub (Metric.mem_ball_self (by positivity))))
  convert hlocal using 1
  field_simp [hd.ne']
  ring


theorem isingFermionic_unitStrip_im_fourthTensor_le_on_halfBall
    (Phi : Complex -> Complex) (c : Complex) (d : Real)
    (hd : 0 < d)
    (hPhi : DifferentiableOn Complex Phi (ball c d))
    (hrange : forall z, z ∈ ball c d ->
      0 <= (Phi z).im /\ (Phi z).im <= 1) :
    forall w, w ∈ ball c (d / 2) ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <=
        12288 / d ^ 4 := by
  intro w hw
  have hsub := isingFermionic_ball_half_subset_ball_of_mem hw
  have hlocal := isingFermionic_strip_im_fourth_tensor
    Phi w (d / 2) (by positivity)
    (hPhi.mono hsub) (fun z hz => hrange z (hsub hz))
  convert hlocal using 1
  field_simp [hd.ne']
  ring

end
