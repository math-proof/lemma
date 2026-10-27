/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import Def.Analysis.SpecialFunctions.Part1Ch9Entry25Dixon.Part4
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry25Dixon

open scoped Topology

open Filter

noncomputable section

theorem dixon_hasDerivAt_V (u : ℂ) (hu10 : u - 1 ≠ 0) :
    HasDerivAt dixonV ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2) u := by
  have h2 : HasDerivAt (fun v : ℂ => v - 1) ((1 : ℂ) - 0) u :=
    (hasDerivAt_id (x := u)).sub (hasDerivAt_const (x := u) (c := (1 : ℂ)))
  exact (hasDerivAt_id u).div h2 hu10

theorem dixon_norm_V_lt_one (u : ℂ) (hu2 : u.re < 1 / 2) :
    ‖dixonV u‖ < 1 := by
  have hsq : Complex.normSq u < Complex.normSq (u - 1) := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero]
    nlinarith [hu2]
  have e1 := Complex.sq_norm u
  have e2 := Complex.sq_norm (u - 1)
  rw [← e1, ← e2] at hsq
  have hlt : ‖u‖ < ‖u - 1‖ := lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq
  have hpos : (0 : ℝ) < ‖u - 1‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have e : ‖dixonV u‖ = ‖u‖ / ‖u - 1‖ := by
    unfold dixonV; rw [norm_div]
  rw [e, div_lt_one hpos]
  exact hlt

theorem dixon_F_hasDerivAt_aux (u : ℂ) (hu1 : ‖u‖ < 1) (hu2 : u.re < 1 / 2)
    (hu10 : u - 1 ≠ 0) :
    HasDerivAt dixonF
      (dixonM u + dixonM (dixonV u) * ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2)
        + (1 / 2 : ℂ) * ((((0 : ℂ) - 1) / (1 - u)) * Complex.log (1 - u)
          + Complex.log (1 - u) * (((0 : ℂ) - 1) / (1 - u)))) u := by
  have hLi := dixon_hasDerivAt_Li u hu1
  have hV := dixon_hasDerivAt_V u hu10
  have hmem : (1 : ℂ) - u ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre : ((1 : ℂ) - u).re = 1 - u.re := by
      rw [Complex.sub_re, Complex.one_re]
    rw [hre]; linarith [hu2]
  have hvv : ‖dixonV u‖ < 1 := dixon_norm_V_lt_one u hu2
  have hLiv := dixon_hasDerivAt_Li (dixonV u) hvv
  have hcomp : HasDerivAt (dixonLi ∘ dixonV)
      (dixonM (dixonV u) * ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2)) u :=
    HasDerivAt.comp u hLiv hV
  have h1 : HasDerivAt (fun v : ℂ => (1 : ℂ) - v) ((0 : ℂ) - 1) u :=
    (hasDerivAt_const (x := u) (c := (1 : ℂ))).sub (hasDerivAt_id (x := u))
  have hlog1 : HasDerivAt (fun v : ℂ => Complex.log (1 - v))
      (((0 : ℂ) - 1) / (1 - u)) u :=
    h1.clog hmem
  have hmul := hlog1.mul hlog1
  have hlogpart : HasDerivAt
      (fun v : ℂ => (1 / 2 : ℂ) * (Complex.log (1 - v) * Complex.log (1 - v)))
      ((1 / 2 : ℂ) * ((((0 : ℂ) - 1) / (1 - u)) * Complex.log (1 - u)
        + Complex.log (1 - u) * (((0 : ℂ) - 1) / (1 - u)))) u :=
    HasDerivAt.const_mul (1 / 2 : ℂ) hmul
  exact (hLi.add hcomp).add hlogpart

theorem dixon_M_zero : dixonM 0 = 1 := by
  have hvanish : ∀ b' : ℕ, b' ≠ 0 →
      (0 : ℂ) ^ b' / ((((b' + 1 : ℕ) : ℝ) : ℂ)) = 0 := by
    intro b' hb
    rw [zero_pow hb, zero_div]
  have h1 : (∑' j : ℕ, (0 : ℂ) ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ)))
      = (0 : ℂ) ^ 0 / ((((0 + 1 : ℕ) : ℝ) : ℂ)) :=
    tsum_eq_single 0 (fun b' hb => hvanish b' hb)
  unfold dixonM
  rw [h1]
  simp

theorem dixon_V_zero : dixonV 0 = 0 := by
  unfold dixonV
  simp

theorem dixon_Fderiv_zero (u : ℂ) (hu1 : ‖u‖ < 1) (hu2 : u.re < 1 / 2)
    (hu10 : u - 1 ≠ 0) :
    dixonM u + dixonM (dixonV u) * ((1 * (u - 1) - u * ((1 : ℂ) - 0)) / (u - 1) ^ 2)
      + (1 / 2 : ℂ) * ((((0 : ℂ) - 1) / (1 - u)) * Complex.log (1 - u)
        + Complex.log (1 - u) * (((0 : ℂ) - 1) / (1 - u))) = 0 := by
  by_cases hune : u = 0
  · subst hune
    rw [dixon_V_zero, dixon_M_zero]
    simp only [sub_zero, Complex.log_one, mul_zero, zero_mul, add_zero]
    norm_num
  · have h1u : (1 : ℂ) - u ≠ 0 := by
      have e : (1 : ℂ) - u = -(u - 1) := by ring
      rw [e]; exact neg_ne_zero.mpr hu10
    have hMu : dixonM u = -Complex.log (1 - u) / u := by
      have h := dixon_uM_eq u hu1
      have h' : dixonM u * u = -Complex.log (1 - u) := by
        rw [mul_comm]; exact h
      exact (eq_div_iff hune).mpr h'
    have hv0 : dixonV u ≠ 0 := by
      unfold dixonV
      exact div_ne_zero hune hu10
    have hvv : ‖dixonV u‖ < 1 := dixon_norm_V_lt_one u hu2
    have hMv : dixonM (dixonV u) = -Complex.log (1 - dixonV u) / dixonV u := by
      have h := dixon_uM_eq (dixonV u) hvv
      have h' : dixonM (dixonV u) * dixonV u = -Complex.log (1 - dixonV u) := by
        rw [mul_comm]; exact h
      exact (eq_div_iff hv0).mpr h'
    have h1v : 1 - dixonV u = 1 / (1 - u) := by
      unfold dixonV
      field_simp
      ring
    have harg : ((1 : ℂ) - u).arg ≠ Real.pi := by
      have hb : |((1 : ℂ) - u).arg| < Real.pi / 2 := by
        rw [Complex.abs_arg_lt_pi_div_two_iff]
        left
        have e : ((1 : ℂ) - u).re = 1 - u.re := by
          rw [Complex.sub_re, Complex.one_re]
        rw [e]; linarith [hu2]
      intro hcon
      rw [hcon, abs_of_pos Real.pi_pos] at hb
      linarith [Real.pi_pos]
    have hlog1v : Complex.log (1 - dixonV u) = -Complex.log (1 - u) := by
      rw [h1v, one_div]
      exact Complex.log_inv _ harg
    rw [hMu, hMv, hlog1v]
    unfold dixonV
    field_simp
    ring

theorem dixon_F_hasDerivAt (u : ℂ) (hu1 : ‖u‖ < 1) (hu2 : u.re < 1 / 2)
    (hu10 : u - 1 ≠ 0) : HasDerivAt dixonF 0 u := by
  have hF := dixon_F_hasDerivAt_aux u hu1 hu2 hu10
  have hval := dixon_Fderiv_zero u hu1 hu2 hu10
  rwa [hval] at hF

theorem dixonU_mem {u : ℂ} : u ∈ dixonU ↔ ‖u‖ < 1 ∧ u.re < 1 / 2 := by
  unfold dixonU
  rw [Set.mem_inter_iff, Metric.mem_ball, dist_zero_right]
  simp only [Set.mem_ofPred_eq]

theorem dixonU_open : IsOpen dixonU :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_re continuous_const)

theorem dixonU_pre : IsPreconnected dixonU :=
  ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_lt (1 / 2))).isPreconnected

theorem dixonU_zero : (0 : ℂ) ∈ dixonU := by
  unfold dixonU
  rw [Set.mem_inter_iff, Metric.mem_ball, dist_self]
  refine ⟨by norm_num, ?_⟩
  change (0 : ℂ).re < 1 / 2
  rw [Complex.zero_re]; norm_num

theorem dixon_mem_imp_sub_ne {u : ℂ} (hu : u ∈ dixonU) : u - 1 ≠ 0 := by
  rw [dixonU_mem] at hu
  obtain ⟨_, hx2⟩ := hu
  intro hcon
  rw [sub_eq_zero.mp hcon, Complex.one_re] at hx2
  norm_num at hx2

theorem dixon_F_const (u : ℂ) (hu : u ∈ dixonU) : dixonF u = dixonF 0 := by
  have hdiff : DifferentiableOn ℂ dixonF dixonU := by
    intro x hx
    rw [dixonU_mem] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxU : x ∈ dixonU := dixonU_mem.mpr ⟨hx1, hx2⟩
    have hFx := dixon_F_hasDerivAt x hx1 hx2 (dixon_mem_imp_sub_ne hxU)
    exact hFx.differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv dixonF) 0 dixonU := by
    intro x hx
    rw [dixonU_mem] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxU : x ∈ dixonU := dixonU_mem.mpr ⟨hx1, hx2⟩
    exact (dixon_F_hasDerivAt x hx1 hx2 (dixon_mem_imp_sub_ne hxU)).deriv
  exact IsOpen.is_const_of_deriv_eq_zero dixonU_open dixonU_pre hdiff hderiv hu dixonU_zero

theorem dixon_F_zero : dixonF 0 = 0 := by
  have hLi0 : dixonLi 0 = 0 := by
    have h0 : ∀ j : ℕ, dixonL (0 : ℂ) j = 0 := by
      intro j
      unfold dixonL
      rw [zero_pow (by omega : j + 1 ≠ 0), zero_div]
    calc dixonLi 0 = ∑' _ : ℕ, (0 : ℂ) := tsum_congr (fun j => h0 j)
      _ = 0 := tsum_zero
  have hv0 : dixonV 0 = 0 := dixon_V_zero
  unfold dixonF
  rw [hLi0, hv0, hLi0]
  simp

theorem dixon_tsum_re (x theta : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (dixonLi ((x : ℂ) * Complex.exp (Complex.I * theta))).re
      = ∑' j : ℕ, chapter9DilogCosTerm x theta j := by
  have hnorm : ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ ≤ 1 := by
    rw [dixon_norm_z x theta h0]; exact h1
  have hs := dixon_summable_Lterm _ hnorm
  unfold dixonLi
  rw [Complex.re_tsum hs]
  exact tsum_congr (fun j => dixon_Lterm_re x theta j)

theorem dixon_tsum_im (x theta : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (dixonLi ((x : ℂ) * Complex.exp (Complex.I * theta))).im
      = ∑' j : ℕ, chapter9DilogSinTerm x theta j := by
  have hnorm : ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ ≤ 1 := by
    rw [dixon_norm_z x theta h0]; exact h1
  have hs := dixon_summable_Lterm _ hnorm
  unfold dixonLi
  rw [Complex.im_tsum hs]
  exact tsum_congr (fun j => dixon_Lterm_im x theta j)

theorem dixon_Li_continuousOn :
    ContinuousOn dixonLi (Metric.closedBall (0 : ℂ) 1) := by
  have hcont : ∀ j : ℕ,
      ContinuousOn (fun v : ℂ => dixonL v j) (Metric.closedBall (0 : ℂ) 1) := by
    intro j
    have hne : ∀ v : ℂ, v ∈ Metric.closedBall (0 : ℂ) 1 →
        ((((j + 1 : ℕ) : ℝ) : ℂ) ^ 2) ≠ 0 := by
      intro v _
      have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
      have hc : ((((j + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      exact pow_ne_zero 2 hc
    exact ((continuous_id.pow _).continuousOn).div continuousOn_const hne
  have hbound : ∀ j : ℕ, ∀ v : ℂ, v ∈ Metric.closedBall (0 : ℂ) 1 →
      ‖dixonL v j‖ ≤ 1 / ((((j + 1 : ℕ) : ℝ) ^ 2)) := by
    intro j v hv
    have hmem : ‖v‖ ≤ 1 := by
      have hdist := Metric.mem_closedBall.mp hv
      rwa [dist_zero_right] at hdist
    exact dixon_norm_Lterm_le v hmem j
  have h := continuousOn_tsum (f := fun j (v : ℂ) => dixonL v j)
    (u := fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ) : ℝ) ^ 2)))
    (s := Metric.closedBall (0 : ℂ) 1)
    hcont dixon_aux_summable_inv_sq_shift hbound
  exact h

theorem dixon_ray_mem_U (z : ℂ) (hz1 : ‖z‖ ≤ 1) (hz2 : z.re ≤ 1 / 2)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ((((t : ℝ)) : ℂ) * z) ∈ dixonU := by
  obtain ⟨ht0, ht1⟩ := Set.mem_Ico.mp ht
  rw [dixonU_mem]
  refine ⟨?_, ?_⟩
  · have e : ‖((((t : ℝ)) : ℂ) * z)‖ = t * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [e]
    calc t * ‖z‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hz1 ht0
      _ = t := mul_one t
      _ < 1 := ht1
  · have ere : (((((t : ℝ)) : ℂ) * z)).re = t * z.re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [ere]
    by_cases hzpos : 0 < z.re
    · calc t * z.re < 1 * z.re := mul_lt_mul_of_pos_right ht1 hzpos
        _ = z.re := one_mul _
        _ ≤ 1 / 2 := hz2
    · have hzle : z.re ≤ 0 := le_of_not_gt hzpos
      calc t * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hzle
        _ < 1 / 2 := by norm_num

theorem dixon_F_boundary (z w : ℂ) (hz1 : ‖z‖ ≤ 1) (hz2 : z.re ≤ 1 / 2)
    (hz3 : z ≠ 1) (hw : w = z / (z - 1)) (hw1 : ‖w‖ ≤ 1) :
    dixonLi z + dixonLi w
      + (1 / 2 : ℂ) * (Complex.log (1 - z) * Complex.log (1 - z)) = 0 := by
  have hzne : z - 1 ≠ 0 := sub_ne_zero.mpr hz3
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hz1
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hw1
  have hVw : dixonV z = w := hw.symm
  have hcont_g : Continuous (fun t : ℝ => ((((t : ℝ)) : ℂ) * z)) :=
    Complex.continuous_ofReal.mul continuous_const
  have hg : Tendsto (fun t : ℝ => ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ)) (𝓝 z) := by
    have h := (hcont_g.tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)) (a := (1 : ℝ)))
    simpa using h
  have hIco_nbhd : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Set.Ico (0 : ℝ) 1 :=
    Filter.eventually_of_mem (Ico_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
      (fun t ht => ht)
  have hg_in : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      ((((t : ℝ)) : ℂ) * z) ∈ Metric.closedBall (0 : ℂ) 1 := by
    filter_upwards [hIco_nbhd] with t ht
    have hUmem := dixon_ray_mem_U z hz1 hz2 t ht
    obtain ⟨hnorm, _⟩ := dixonU_mem.mp hUmem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm.le
  have hg_sub : Tendsto (fun t : ℝ => ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝[Metric.closedBall (0 : ℂ) 1] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hg hg_in
  have hLiz : Tendsto (fun t : ℝ => dixonLi ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (dixonLi z)) :=
    Filter.Tendsto.congr (fun t => rfl)
      (Filter.Tendsto.comp
        (dixon_Li_continuousOn.continuousWithinAt hzmem) hg_sub)
  have hVcont : ContinuousAt dixonV z := (dixon_hasDerivAt_V z hzne).continuousAt
  have hVg : Tendsto (fun t : ℝ => dixonV ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (dixonV z)) :=
    Filter.Tendsto.congr (fun t => rfl) (Filter.Tendsto.comp hVcont hg)
  rw [hVw] at hVg
  have hVg_in : ∀ᶠ t in 𝓝[<] (1 : ℝ),
      dixonV ((((t : ℝ)) : ℂ) * z) ∈ Metric.closedBall (0 : ℂ) 1 := by
    filter_upwards [hIco_nbhd] with t ht
    have hUmem := dixon_ray_mem_U z hz1 hz2 t ht
    have hlt := dixon_norm_V_lt_one _ (dixonU_mem.mp hUmem).2
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hlt.le
  have hVg_sub : Tendsto (fun t : ℝ => dixonV ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝[Metric.closedBall (0 : ℂ) 1] w) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hVg hVg_in
  have hLiw : Tendsto (fun t : ℝ => dixonLi (dixonV ((((t : ℝ)) : ℂ) * z)))
      (𝓝[<] (1 : ℝ)) (𝓝 (dixonLi (dixonV z))) := by
    have h := Filter.Tendsto.congr (fun t => rfl)
      (Filter.Tendsto.comp
        (dixon_Li_continuousOn.continuousWithinAt hwmem) hVg_sub)
    rwa [← hVw] at h
  have h1zslit : (1 : ℂ) - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have e : ((1 : ℂ) - z).re = 1 - z.re := by
      rw [Complex.sub_re, Complex.one_re]
    rw [e]; linarith [hz2]
  have hlogc : ContinuousAt Complex.log (1 - z) := continuousAt_clog h1zslit
  have h1g : Tendsto (fun t : ℝ => (1 : ℂ) - ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (1 - z)) :=
    tendsto_const_nhds.sub hg
  have hlogtend : Tendsto
      (fun t : ℝ => Complex.log (1 - ((((t : ℝ)) : ℂ) * z))) (𝓝[<] (1 : ℝ))
      (𝓝 (Complex.log (1 - z))) :=
    Filter.Tendsto.congr (fun t => rfl) (Filter.Tendsto.comp hlogc h1g)
  have hlogpart : Tendsto
      (fun t : ℝ => (1 / 2 : ℂ)
        * (Complex.log (1 - ((((t : ℝ)) : ℂ) * z))
          * Complex.log (1 - ((((t : ℝ)) : ℂ) * z))))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((1 / 2 : ℂ) * (Complex.log (1 - z) * Complex.log (1 - z)))) :=
    tendsto_const_nhds.mul (hlogtend.mul hlogtend)
  have hlim : Tendsto (fun t : ℝ => dixonF ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (dixonF z)) := by
    have h := (hLiz.add hLiw).add hlogpart
    simpa only [dixonF] using h
  have hF0 : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 → dixonF ((((t : ℝ)) : ℂ) * z) = 0 := by
    intro t ht
    have hUmem := dixon_ray_mem_U z hz1 hz2 t ht
    rw [dixon_F_const _ hUmem, dixon_F_zero]
  have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun t => dixonF ((((t : ℝ)) : ℂ) * z)) :=
    Filter.eventually_of_mem (Ico_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
      (fun t ht => (hF0 t ht).symm)
  have hconst : Tendsto (fun t : ℝ => dixonF ((((t : ℝ)) : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 0) :=
    Tendsto.congr' heq tendsto_const_nhds
  have hFz : dixonF z = 0 := tendsto_nhds_unique hlim hconst
  unfold dixonF at hFz
  rwa [hVw] at hFz

theorem dixon_claim (z w : ℂ) (hz2 : z.re ≤ 1 / 2) (hz3 : z ≠ 1)
    (hw : w = z / (z - 1))
    (hFz : dixonLi z + dixonLi w
      + (1 / 2 : ℂ) * (Complex.log (1 - z) * Complex.log (1 - z)) = 0) :
    dixonLi z + dixonLi w
      = (1 / 2 : ℂ) * Complex.log (1 - z) * Complex.log (1 - w) := by
  have hu10 : z - 1 ≠ 0 := sub_ne_zero.mpr hz3
  have h1u : (1 : ℂ) - z ≠ 0 := by
    have e : (1 : ℂ) - z = -(z - 1) := by ring
    rw [e]; exact neg_ne_zero.mpr hu10
  have harg : ((1 : ℂ) - z).arg ≠ Real.pi := by
    have hb : |((1 : ℂ) - z).arg| < Real.pi / 2 := by
      rw [Complex.abs_arg_lt_pi_div_two_iff]
      left
      have e : ((1 : ℂ) - z).re = 1 - z.re := by
        rw [Complex.sub_re, Complex.one_re]
      rw [e]; linarith [hz2]
    intro hcon
    rw [hcon, abs_of_pos Real.pi_pos] at hb
    linarith [Real.pi_pos]
  have h1w : (1 : ℂ) - w = (1 - z)⁻¹ := by
    rw [hw]
    field_simp
    ring
  have hlogw : Complex.log (1 - w) = -Complex.log (1 - z) := by
    rw [h1w]
    exact Complex.log_inv _ harg
  rw [hlogw]
  linear_combination hFz

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry25_dixon`.
-/
theorem ramanujan_part1_ch9_entry25_dixon (x y theta phi : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) =
        (x * y : ℝ) * Complex.exp (Complex.I * (theta + phi))) :
    let Ax := 1 - 2 * x * Real.cos theta + x ^ 2
    let Ay := 1 - 2 * y * Real.cos phi + y ^ 2
    let ux := Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta))
    let uy := Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi))
    1 - x * Real.cos theta ≠ 0 ∧
      1 - y * Real.cos phi ≠ 0 ∧
      0 < Ax ∧ 0 < Ay ∧
      Summable (chapter9DilogCosTerm x theta) ∧
      Summable (chapter9DilogCosTerm y phi) ∧
      Summable (chapter9DilogSinTerm x theta) ∧
      Summable (chapter9DilogSinTerm y phi) ∧
      (∑' j : ℕ, chapter9DilogCosTerm x theta j) +
          ∑' j : ℕ, chapter9DilogCosTerm y phi j =
        Real.log Ax * Real.log Ay / 8 - ux * uy / 2 ∧
      (∑' j : ℕ, chapter9DilogSinTerm x theta j) +
          ∑' j : ℕ, chapter9DilogSinTerm y phi j =
        -Real.log Ax * uy / 4 - Real.log Ay * ux / 4 := by
  have hxy' := dixon_zw_mul x y theta phi hxy
  have hnormz : ‖((x : ℂ) * Complex.exp (Complex.I * theta))‖ ≤ 1 := by
    rw [dixon_norm_z x theta hx.1]; exact hx.2
  have hnormw : ‖((y : ℂ) * Complex.exp (Complex.I * phi))‖ ≤ 1 := by
    rw [dixon_norm_z y phi hy.1]; exact hy.2
  have hrez : ((((x : ℂ) * Complex.exp (Complex.I * theta)))).re ≤ 1 / 2 :=
    dixon_re_le_half x y theta phi hxy' hnormw
  have hrew : ((((y : ℂ) * Complex.exp (Complex.I * phi)))).re ≤ 1 / 2 :=
    dixon_re_le_half y x phi theta (by linear_combination hxy') hnormz
  have hz_ne : ((x : ℂ) * Complex.exp (Complex.I * theta)) ≠ 1 :=
    dixon_z_ne_one x y theta phi hxy'
  have hw_eq : ((y : ℂ) * Complex.exp (Complex.I * phi))
      = ((x : ℂ) * Complex.exp (Complex.I * theta))
        / (((x : ℂ) * Complex.exp (Complex.I * theta)) - 1) :=
    dixon_w_eq_div x y theta phi hxy' hz_ne
  have hFz := dixon_F_boundary _ _ hnormz hrez hz_ne hw_eq hnormw
  have hclaim := dixon_claim _ _ hrez hz_ne hw_eq hFz
  have hAx_pos := dixon_side_pos x theta hrez
  have hAy_pos := dixon_side_pos y phi hrew
  have hnvx := dixon_side_nonvanish x theta hrez
  have hnvy := dixon_side_nonvanish y phi hrew
  have hsCx := dixon_summable_dilogCos x theta hx.1 hx.2
  have hsCy := dixon_summable_dilogCos y phi hy.1 hy.2
  have hsSx := dixon_summable_dilogSin x theta hx.1 hx.2
  have hsSy := dixon_summable_dilogSin y phi hy.1 hy.2
  have hcos_re_x := dixon_tsum_re x theta hx.1 hx.2
  have hcos_re_y := dixon_tsum_re y phi hy.1 hy.2
  have hsin_im_x := dixon_tsum_im x theta hx.1 hx.2
  have hsin_im_y := dixon_tsum_im y phi hy.1 hy.2
  have hhalf_x : (1 : ℝ) / 2 ≤ 1 - x * Real.cos theta := by
    have h := hrez; rw [dixon_re_z] at h; linarith
  have hhalf_y : (1 : ℝ) / 2 ≤ 1 - y * Real.cos phi := by
    have h := hrew; rw [dixon_re_z] at h; linarith
  have hPre := dixon_log_one_sub_z_re x theta hAx_pos
  have hPim := dixon_log_one_sub_z_im x theta hhalf_x
  have hQre := dixon_log_one_sub_z_re y phi hAy_pos
  have hQim := dixon_log_one_sub_z_im y phi hhalf_y
  have e12 : ((1 / 2 : ℂ)) = ((((1 / 2 : ℝ)) : ℂ)) := by simp
  have hre0 := congrArg Complex.re hclaim
  have him0 := congrArg Complex.im hclaim
  rw [Complex.add_re, hcos_re_x, hcos_re_y, e12, Complex.mul_re, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hPre, hPim, hQre,
    hQim] at hre0
  rw [Complex.add_im, hsin_im_x, hsin_im_y, e12, Complex.mul_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hPre, hPim, hQre,
    hQim] at him0
  intro Ax Ay ux uy
  refine ⟨hnvx, hnvy, hAx_pos, hAy_pos, hsCx, hsCy, hsSx, hsSy, ?_, ?_⟩
  · change (∑' j : ℕ, chapter9DilogCosTerm x theta j)
          + (∑' j : ℕ, chapter9DilogCosTerm y phi j)
        = Real.log (1 - 2 * x * Real.cos theta + x ^ 2)
          * Real.log (1 - 2 * y * Real.cos phi + y ^ 2) / 8
          - Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta))
            * Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi)) / 2
    linear_combination hre0
  · change (∑' j : ℕ, chapter9DilogSinTerm x theta j)
          + (∑' j : ℕ, chapter9DilogSinTerm y phi j)
        = -Real.log (1 - 2 * x * Real.cos theta + x ^ 2)
          * Real.arctan (y * Real.sin phi / (1 - y * Real.cos phi)) / 4
          - Real.log (1 - 2 * y * Real.cos phi + y ^ 2)
            * Real.arctan (x * Real.sin theta / (1 - x * Real.cos theta)) / 4
    linear_combination him0

end
end Entry25Dixon
end Ramanujan.Part1Ch9
end
