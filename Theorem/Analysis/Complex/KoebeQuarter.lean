/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Koebe one-quarter theorem
-/


section

namespace Complex.KoebeQuarterWanted

open MeasureTheory

theorem exists_log_of_ne_zero_on_ball
    (c : ℂ) (R : ℝ) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball c R))
    (hne : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (a : ℂ) (ha : Complex.exp a = g c)
    (hmem : c ∈ Metric.ball c R) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Metric.ball c R) ∧ L c = a ∧
      ∀ z ∈ Metric.ball c R, Complex.exp (L z) = g z := by
  have hopen : IsOpen (Metric.ball c R) := Metric.isOpen_ball
  have hR : 0 < R := by
    rw [Metric.mem_ball, dist_self] at hmem
    exact hmem
  have hg' : DifferentiableOn ℂ (deriv g) (Metric.ball c R) :=
    hg.deriv hopen
  have hlog : DifferentiableOn ℂ (fun z => deriv g z / g z) (Metric.ball c R) :=
    hg'.div hg hne
  have hexact : Complex.IsExactOn (fun z => deriv g z / g z) (Metric.ball c R) :=
    hlog.isExactOn_ball
  obtain ⟨L, hLc, hL⟩ := hexact.with_val_at c a
  refine ⟨L, ?_, hLc, ?_⟩
  · exact (fun z hz => (hL z hz).differentiableAt.differentiableWithinAt)
  · have hE : ∀ z ∈ Metric.ball c R, Complex.exp (-L z) * g z = 1 := by
      have hEderiv : ∀ z ∈ Metric.ball c R,
          HasDerivAt (fun w => Complex.exp (-L w) * g w) 0 z := by
        intro z hz
        have h1 : HasDerivAt L (deriv g z / g z) z := hL z hz
        have hexp : HasDerivAt (fun w => Complex.exp (-L w))
            (-Complex.exp (-L z) * (deriv g z / g z)) z := by
          have hneg : HasDerivAt (fun w => -L w) (-(deriv g z / g z)) z :=
            h1.neg
          have := hneg.cexp
          simpa [mul_comm] using this
        have hg1 : HasDerivAt g (deriv g z) z :=
          hg.hasDerivAt (hopen.mem_nhds hz)
        have hmul := hexp.mul hg1
        have hgz : g z ≠ 0 := hne z hz
        have hzero : -Complex.exp (-L z) * (deriv g z / g z) * g z +
            Complex.exp (-L z) * deriv g z = 0 := by
          field_simp
          ring
        have hfun : ((fun w => Complex.exp (-L w)) * g) = (fun w => Complex.exp (-L w) * g w) := rfl
        rw [hfun] at hmul
        rw [hzero] at hmul
        exact hmul
      have hEdiff : DifferentiableOn ℂ (fun w => Complex.exp (-L w) * g w) (Metric.ball c R) :=
        fun z hz => (hEderiv z hz).differentiableAt.differentiableWithinAt
      have hEqOn : Set.EqOn (deriv (fun w => Complex.exp (-L w) * g w)) 0 (Metric.ball c R) := by
        intro w hw
        have h := (hEderiv w hw).deriv
        simpa using h
      have hconst : ∀ x ∈ Metric.ball c R, ∀ y ∈ Metric.ball c R,
          (fun w => Complex.exp (-L w) * g w) x = (fun w => Complex.exp (-L w) * g w) y := by
        intro x hx y hy
        exact hopen.is_const_of_deriv_eq_zero
          (convex_ball c R |>.isPreconnected) hEdiff hEqOn hx hy
      have hEc : Complex.exp (-L c) * g c = 1 := by
        rw [← ha]
        rw [← Complex.exp_add]
        simp [hLc]
      intro z hz
      have hcc := hconst z hz c hmem
      simpa [hEc] using hcc
    intro z hz
    have h1 := hE z hz
    have hexp0 : Complex.exp (-L z) ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp (-L z) * g z = Complex.exp (-L z) * Complex.exp (L z) := by
      rw [h1]
      rw [← Complex.exp_add]
      simp
    have h3 : g z = Complex.exp (L z) := (mul_left_cancel₀ hexp0 h2)
    exact h3.symm

theorem exists_sqrt_of_univalent
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (h0 : f 0 = 0)
    (hderiv : deriv f 0 = 1) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1) ∧ s 0 = 1 ∧
      (∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0) ∧
      ∀ w ∈ Metric.ball (0 : ℂ) 1, w * s w ^ 2 = f w := by
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hphi : DifferentiableOn ℂ (dslope f 0) (Metric.ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope hnhds).mpr hf
  have hphi0 : dslope f 0 0 = 1 := by rw [dslope_same, hderiv]
  have hmul_eq : ∀ w : ℂ, w * dslope f 0 w = f w := by
    intro w
    have h := sub_smul_dslope f 0 w
    simpa [h0, smul_eq_mul] using h
  have hphine : ∀ w ∈ Metric.ball (0 : ℂ) 1, dslope f 0 w ≠ 0 := by
    intro w hw hcon
    by_cases hw0 : w = 0
    · rw [hw0, hphi0] at hcon; exact one_ne_zero hcon
    · have h2 := hmul_eq w
      rw [hcon, mul_zero] at h2
      have hfw : f w = f 0 := by rw [← h2, h0]
      have heq := hinj hw hmem0 hfw
      exact hw0 heq
  obtain ⟨L, hLdiff, hL0, hLexp⟩ :=
    exists_log_of_ne_zero_on_ball 0 1 (dslope f 0) hphi hphine 0
      (by rw [hphi0, Complex.exp_zero]) hmem0
  refine ⟨fun w => Complex.exp (L w / 2), ?_, ?_, ?_, ?_⟩
  · exact (hLdiff.div_const 2).cexp
  · simp [hL0]
  · intro w _
    exact Complex.exp_ne_zero _
  · intro w hw
    have hsq : (Complex.exp (L w / 2)) ^ 2 = dslope f 0 w := by
      have h1 : Complex.exp (L w / 2) ^ 2 =
          Complex.exp (L w / 2 + L w / 2) := by
        rw [sq, ← Complex.exp_add]
      rw [h1]
      have h2 : L w / 2 + L w / 2 = L w := by ring
      rw [h2, hLexp w hw]
    rw [hsq]
    exact hmul_eq w

theorem koebe_inv_sqrt_expansion
    (s : ℂ → ℂ)
    (hs : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1))
    (hs0 : s 0 = 1)
    (hsne : ∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0) :
    let k := dslope (fun w => (s w)⁻¹) 0
    DifferentiableOn ℂ k (Metric.ball (0 : ℂ) 1) ∧
    (∀ w : ℂ, (s w)⁻¹ = 1 + w * k w) ∧
    k 0 = -deriv s 0 := by
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hinv : DifferentiableOn ℂ (fun w => (s w)⁻¹) (Metric.ball (0 : ℂ) 1) :=
    hs.inv hsne
  have hk : DifferentiableOn ℂ (dslope (fun w => (s w)⁻¹) 0) (Metric.ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope hnhds).mpr hinv
  refine ⟨hk, ?_, ?_⟩
  · intro w
    have h := sub_smul_dslope (fun w => (s w)⁻¹) 0 w
    have h0inv : ((s (0 : ℂ))⁻¹) = 1 := by rw [hs0, inv_one]
    have h2 : w * dslope (fun w => (s w)⁻¹) 0 w = (s w)⁻¹ - 1 := by
      simpa [h0inv, smul_eq_mul, sub_zero] using h
    linear_combination -h2
  · have hds : dslope (fun w => (s w)⁻¹) 0 0
      = deriv (fun w => (s w)⁻¹) 0 := dslope_same _ _
    rw [hds]
    have hs0at : HasDerivAt s (deriv s 0) 0 :=
      hs.hasDerivAt (Metric.isOpen_ball.mem_nhds hmem0)
    have hinv_at := hs0at.inv (by rw [hs0]; exact one_ne_zero)
    have hder : deriv (fun w => (s w)⁻¹) 0 = -deriv s 0 / s 0 ^ 2 :=
      hinv_at.deriv
    rw [hder, hs0]
    simp

theorem deriv_sqrt_eq_iteratedDeriv_two
    (f s : ℂ → ℂ)
    (hs : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) 1))
    (hs0 : s 0 = 1)
    (heq : ∀ w ∈ Metric.ball (0 : ℂ) 1, w * s w ^ 2 = f w) :
    deriv s 0 = iteratedDeriv 2 f 0 / 4 := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hev : (fun w => w * s w ^ 2) =ᶠ[nhds (0 : ℂ)] f :=
    Filter.eventually_of_mem hnhds (fun w hw => heq w hw)
  have hiter : iteratedDeriv 2 (fun w => w * s w ^ 2) 0 = iteratedDeriv 2 f 0 :=
    Filter.EventuallyEq.iteratedDeriv_eq 2 hev
  have hs' : DifferentiableOn ℂ (deriv s) (Metric.ball (0 : ℂ) 1) :=
    hs.deriv hopen
  have hsq_at : ∀ w : ℂ, HasDerivAt s (deriv s w) w →
      HasDerivAt (fun w => s w ^ 2) (2 * s w * deriv s w) w := by
    intro w hsw
    have h := hsw.mul hsw
    have hfun : (s * s) = (fun w => s w ^ 2) := by ext x; simp [sq, Pi.mul_apply]
    have hder : deriv s w * s w + s w * deriv s w = 2 * s w * deriv s w := by ring
    rw [hfun, hder] at h
    exact h
  have hderiv1 : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      HasDerivAt (fun w => w * s w ^ 2)
        (s w ^ 2 + w * (2 * s w * deriv s w)) w := by
    intro w hw
    have hsw : HasDerivAt s (deriv s w) w :=
      hs.hasDerivAt (hopen.mem_nhds hw)
    have hsq := hsq_at w hsw
    have hid : HasDerivAt (fun w : ℂ => w) 1 w := hasDerivAt_id w
    have hmul := hid.mul hsq
    have hfun : ((fun w : ℂ => w) * (fun w => s w ^ 2)) = (fun w => w * s w ^ 2) := rfl
    have hder : (1 : ℂ) * s w ^ 2 + w * (2 * s w * deriv s w) =
        s w ^ 2 + w * (2 * s w * deriv s w) := by ring
    rw [hfun, hder] at hmul
    exact hmul
  have h1 : deriv (fun w => w * s w ^ 2) =ᶠ[nhds (0 : ℂ)]
      (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) := by
    apply Filter.eventually_of_mem hnhds
    intro w hw
    exact (hderiv1 w hw).deriv
  have h2 : deriv (deriv (fun w => w * s w ^ 2)) 0 =
      deriv (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) 0 :=
    Filter.EventuallyEq.deriv_eq h1
  have hsw0 : HasDerivAt s (deriv s 0) 0 :=
    hs.hasDerivAt (hopen.mem_nhds hmem0)
  have hsp0 : HasDerivAt (deriv s) (deriv (deriv s) 0) 0 :=
    hs'.hasDerivAt (hopen.mem_nhds hmem0)
  have hsq0 : HasDerivAt (fun w => s w ^ 2) (2 * s 0 * deriv s 0) 0 :=
    hsq_at 0 hsw0
  have hinner : HasDerivAt (fun w : ℂ => 2 * s w * deriv s w)
      (2 * (deriv s 0 * deriv s 0 + s 0 * deriv (deriv s) 0)) 0 := by
    have e1 : HasDerivAt (fun w => s w * deriv s w)
        (deriv s 0 * deriv s 0 + s 0 * deriv (deriv s) 0) 0 :=
      hsw0.mul hsp0 |>.congr_of_eventuallyEq (by filter_upwards with x; simp [Pi.mul_apply])
    have e2 := e1.const_mul (2 : ℂ)
    have hfun12 : (fun w : ℂ => 2 * s w * deriv s w) =ᶠ[nhds (0 : ℂ)]
        (fun y => 2 * (s y * deriv s y)) := by
      filter_upwards with x; ring
    exact e2.congr_of_eventuallyEq hfun12
  have hprod0 : HasDerivAt (fun w : ℂ => w * (2 * s w * deriv s w))
      (2 * s 0 * deriv s 0) 0 := by
    have hmul := (hasDerivAt_id (0 : ℂ)).mul hinner
    have hder_eq : (1 : ℂ) * (2 * s 0 * deriv s 0) +
        id 0 * (2 * (deriv s 0 * deriv s 0 + s 0 * deriv (deriv s) 0)) =
        2 * s 0 * deriv s 0 := by
      simp only [id_eq]
      ring
    rw [hder_eq] at hmul
    have hfun12 : (fun w : ℂ => w * (2 * s w * deriv s w)) =ᶠ[nhds (0 : ℂ)]
        ((id : ℂ → ℂ) * (fun w : ℂ => 2 * s w * deriv s w)) := by
      filter_upwards with x; simp [Pi.mul_apply, id_eq]
    exact hmul.congr_of_eventuallyEq hfun12
  have hsum0 : HasDerivAt (fun w => s w ^ 2 + w * (2 * s w * deriv s w))
      (4 * deriv s 0) 0 := by
    have h := hsq0.add hprod0
    have hder_eq : 2 * s 0 * deriv s 0 + 2 * s 0 * deriv s 0 = 4 * deriv s 0 := by
      rw [hs0]; ring
    rw [hder_eq] at h
    have hfun12 : (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) =ᶠ[nhds (0 : ℂ)]
        ((fun w => s w ^ 2) + (fun w : ℂ => w * (2 * s w * deriv s w))) := by
      filter_upwards with x; simp [Pi.add_apply]
    exact h.congr_of_eventuallyEq hfun12
  have hval : deriv (fun w => s w ^ 2 + w * (2 * s w * deriv s w)) 0 =
      4 * deriv s 0 := hsum0.deriv
  have hiter2 : iteratedDeriv 2 (fun w => w * s w ^ 2) 0 = 4 * deriv s 0 := by
    have e1 : iteratedDeriv 2 (fun w => w * s w ^ 2) =
        deriv (deriv (fun w => w * s w ^ 2)) := by
      have : (2 : ℕ) = 1 + 1 := rfl
      rw [this, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e1, h2, hval]
  rw [hiter] at hiter2
  rw [hiter2]
  ring

theorem koebe_G_injOn
    (f s k G : ℂ → ℂ)
    (hsne : ∀ w ∈ Metric.ball (0 : ℂ) 1, s w ≠ 0)
    (heq : ∀ w ∈ Metric.ball (0 : ℂ) 1, w * s w ^ 2 = f w)
    (hkinv : ∀ w : ℂ, (s w)⁻¹ = 1 + w * k w)
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1)) :
    (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → z ^ 2 ∈ Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → G z = (z * s (z ^ 2))⁻¹) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → G z ≠ 0) ∧
    Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}) := by
  have hsq_mem : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → z ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz _
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  have hGinv : ∀ z : ℂ, z ≠ 0 → G z = (z * s (z ^ 2))⁻¹ := by
    intro z hzne
    have h1 := hkinv (z ^ 2)
    rw [hG z, mul_inv, h1]
    field_simp
  refine ⟨hsq_mem, fun z hz hzne => hGinv z hzne, ?_, ?_⟩
  · intro z hz hzne
    rw [hGinv z hzne]
    have hmem2 : z ^ 2 ∈ Metric.ball (0 : ℂ) 1 := hsq_mem z hz hzne
    have hs2 : s (z ^ 2) ≠ 0 := hsne _ hmem2
    exact inv_ne_zero (mul_ne_zero hzne hs2)
  · intro z1 hz1 z2 hz2 heq12
    have hz1m : z1 ∈ Metric.ball (0 : ℂ) 1 := hz1.1
    have hz2m : z2 ∈ Metric.ball (0 : ℂ) 1 := hz2.1
    have hn1 : z1 ≠ 0 := fun h => hz1.2 (Set.mem_singleton_iff.mpr h)
    have hn2 : z2 ≠ 0 := fun h => hz2.2 (Set.mem_singleton_iff.mpr h)
    have hm1 : z1 ^ 2 ∈ Metric.ball (0 : ℂ) 1 := hsq_mem z1 hz1m hn1
    have hm2 : z2 ^ 2 ∈ Metric.ball (0 : ℂ) 1 := hsq_mem z2 hz2m hn2
    have hG1 : G z1 = (z1 * s (z1 ^ 2))⁻¹ := hGinv z1 hn1
    have hG2 : G z2 = (z2 * s (z2 ^ 2))⁻¹ := hGinv z2 hn2
    have h12 : z1 * s (z1 ^ 2) = z2 * s (z2 ^ 2) := by
      rw [hG1, hG2] at heq12
      exact inv_inj.mp heq12
    have hsq12 : f (z1 ^ 2) = f (z2 ^ 2) := by
      have e1 := heq _ hm1
      have e2 := heq _ hm2
      have q1 : (z1 * s (z1 ^ 2)) ^ 2 = f (z1 ^ 2) := by
        rw [mul_pow]; exact e1
      have q2 : (z2 * s (z2 ^ 2)) ^ 2 = f (z2 ^ 2) := by
        rw [mul_pow]; exact e2
      rw [← q1, ← q2, h12]
    have hsq_eq := hinj hm1 hm2 hsq12
    have hor := sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq
    rcases hor with h | h
    · exact h
    · exfalso
      have hsq2 : z1 ^ 2 = z2 ^ 2 := by rw [h]; ring
      have hs12 : s (z1 ^ 2) = s (z2 ^ 2) := by rw [hsq2]
      have hz2 : z2 = -z1 := by linear_combination h
      have hsq3 : (-z1) ^ 2 = z1 ^ 2 := by ring
      have hcontra : z1 * s (z1 ^ 2) = -(z1 * s (z1 ^ 2)) := by
        rw [hz2] at h12
        rw [hsq3] at h12
        linear_combination h12
      have h2z : (2 : ℂ) * (z1 * s (z1 ^ 2)) = 0 := by linear_combination hcontra
      have hs1 : s (z1 ^ 2) ≠ 0 := hsne _ hm1
      have hzz : z1 = 0 := by
        rcases mul_eq_zero.mp h2z with h2 | hz
        · norm_num at h2
        · rcases mul_eq_zero.mp hz with hzz | hss
          · exact hzz
          · exact absurd hss hs1
      exact hn1 hzz

theorem koebe_G_hasDerivAt
    (k G : ℂ → ℂ)
    (hk : DifferentiableOn ℂ k (Metric.ball (0 : ℂ) 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2)) :
    let u := fun z : ℂ => z * k (z ^ 2)
    let m := deriv u
    let c := k 0
    DifferentiableOn ℂ u (Metric.ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1) ∧
    m 0 = c ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
      HasDerivAt G (-(z ^ 2)⁻¹ + m z) z := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hmaps : Set.MapsTo (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have h1 : ‖z‖ < 1 := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    rw [Metric.mem_ball, dist_zero_right, norm_pow]
    have hnn : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ - 1)]
  have hsq_diff : DifferentiableOn ℂ (fun z : ℂ => z ^ 2) (Metric.ball (0 : ℂ) 1) :=
    DifferentiableOn.pow differentiableOn_id 2
  have hcomp : DifferentiableOn ℂ (fun z : ℂ => k (z ^ 2)) (Metric.ball (0 : ℂ) 1) :=
    hk.comp hsq_diff hmaps
  have hu : DifferentiableOn ℂ (fun z : ℂ => z * k (z ^ 2)) (Metric.ball (0 : ℂ) 1) :=
    differentiableOn_id.mul hcomp
  refine ⟨hu, hu.deriv hopen, ?_, ?_⟩
  · show deriv (fun z : ℂ => z * k (z ^ 2)) 0 = k 0
    have hsq0 : HasDerivAt (fun z : ℂ => z ^ 2) ((2 : ℂ) * 0 ^ (2 - 1)) 0 :=
      hasDerivAt_pow 2 0
    have hk0 : HasDerivAt k (deriv k ((0 : ℂ) ^ 2)) ((0 : ℂ) ^ 2) := by
      have hmem : ((0 : ℂ) ^ 2) ∈ Metric.ball (0 : ℂ) 1 := by simp [hmem0]
      exact hk.hasDerivAt (hopen.mem_nhds hmem)
    have hcomp0 :
        HasDerivAt (fun z : ℂ => k (z ^ 2))
          (deriv k ((0 : ℂ) ^ 2) * ((2 : ℂ) * 0 ^ (2 - 1))) 0 :=
      (HasDerivAt.comp (0 : ℂ) (h := fun z : ℂ => z ^ 2) hk0
        hsq0).congr_of_eventuallyEq (by
        filter_upwards with x
        simp)
    have hu0 := (hasDerivAt_id (0 : ℂ)).mul hcomp0
    have hder_eq : (1 : ℂ) * k ((0 : ℂ) ^ 2) +
        id 0 * (deriv k ((0 : ℂ) ^ 2) * ((2 : ℂ) * 0 ^ (2 - 1))) = k 0 := by
      simp [id_eq]
    rw [hder_eq] at hu0
    have hfun : ((fun w : ℂ => w) * (fun z : ℂ => k (z ^ 2))) =ᶠ[nhds (0 : ℂ)]
        (fun z : ℂ => z * k (z ^ 2)) := by
      filter_upwards with x; simp [Pi.mul_apply]
    have hu0' := hu0.congr_of_eventuallyEq hfun
    exact hu0'.deriv
  · intro z hz hzne
    have hu_at : HasDerivAt (fun w : ℂ => w * k (w ^ 2)) (deriv (fun w : ℂ => w * k (w ^ 2)) z) z :=
      hu.hasDerivAt (hopen.mem_nhds hz)
    have hinv : HasDerivAt (fun y : ℂ => y⁻¹) (-(z ^ 2)⁻¹) z :=
      hasDerivAt_inv hzne
    have hadd := hinv.add hu_at
    have hfun : (fun w : ℂ => w⁻¹ + w * k (w ^ 2)) =ᶠ[nhds z]
        (((fun y : ℂ => y⁻¹) + (fun w : ℂ => w * k (w ^ 2)))) := by
      filter_upwards with x; simp [Pi.add_apply]
    have hadd' := hadd.congr_of_eventuallyEq hfun
    have hGeq : G = (fun w : ℂ => w⁻¹ + w * k (w ^ 2)) := by
      ext w; rw [hG w]
    rw [hGeq]
    exact hadd'

theorem vol_image_eq_lintegral_norm_deriv_sq
    (S : Set ℂ) (F : ℂ → ℂ) (F' : ℂ → ℂ)
    (hS : MeasurableSet S)
    (hderiv : ∀ z ∈ S, HasDerivAt F (F' z) z)
    (hinj : Set.InjOn F S) :
    volume (F '' S) = ∫⁻ z in S, ENNReal.ofReal (‖F' z‖ ^ 2) := by
  have key : ∀ z ∈ S, HasFDerivWithinAt F
      ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ) S z := by
    intro z hz
    have h1 : HasFDerivAt F (ContinuousLinearMap.toSpanSingleton ℂ (F' z)) z :=
      (hderiv z hz).hasFDerivAt
    have h2 : HasFDerivAt F
        ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ) z :=
      HasFDerivAt.restrictScalars ℝ h1
    exact h2.hasFDerivWithinAt
  have hvol := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
    (E := ℂ) (s := S) (f := F)
    (f' := fun z => (ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ)
    (μ := volume) hS key hinj
  rw [← hvol]
  apply setLIntegral_congr_fun hS
  intro z hz
  have hdet : ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ).det
      = ‖F' z‖ ^ 2 := by
    have e1 : ((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ).det
        = LinearMap.det
          (((ContinuousLinearMap.toSpanSingleton ℂ (F' z)).restrictScalars ℝ) : ℂ →ₗ[ℝ] ℂ) := rfl
    rw [e1, ContinuousLinearMap.coe_restrictScalars]
    have e2 : ((ContinuousLinearMap.toSpanSingleton ℂ (F' z) : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ)
        = LinearMap.toSpanSingleton ℂ ℂ (F' z) := rfl
    rw [e2, LinearMap.det_restrictScalars]
    have e3 : LinearMap.det (LinearMap.toSpanSingleton ℂ ℂ (F' z)) = F' z := by
      have hsm : LinearMap.toSpanSingleton ℂ ℂ (F' z) = (F' z) • LinearMap.id := by
        ext
        simp [LinearMap.toSpanSingleton]
      rw [hsm, LinearMap.det_smul, LinearMap.det_id]
      simp [Module.finrank_self]
    rw [e3]
    rw [Algebra.norm_complex_eq]
    simp [Complex.normSq_eq_norm_sq]
  simp only
  rw [hdet, abs_of_nonneg (by positivity)]

theorem koebe_pointwise_lower
    (m : ℂ → ℂ) (c : ℂ) (t : ℝ) (u : ℂ)
    (ht0 : 0 < t) (hU : ‖u‖ = t) :
    t⁻¹ ^ 4 + ‖c‖ ^ 2
      + 2 * (((starRingEnd ℂ) c * (m u - c)).re)
      - 2 * t⁻¹ ^ 4 * (((u ^ 2 * m u)).re)
      ≤ ‖-(((u ^ 2))⁻¹) + m u‖ ^ 2 := by
  have htne : t ≠ 0 := ne_of_gt ht0
  have ht4 : (t ^ 4 : ℝ) ≠ 0 := pow_ne_zero 4 htne
  have hu0 : u ≠ 0 := by
    intro h
    apply htne
    rw [← hU, h, norm_zero]
  have hconj : ∀ a b : ℂ,
      (a * (starRingEnd ℂ) b).re = ((starRingEnd ℂ) a * b).re := by
    intro a b
    conv_lhs => rw [← Complex.conj_re]
    simp [map_mul]
  have h3 : (starRingEnd ℂ) (u ^ 2)
      = ((t ^ 4 : ℝ) : ℂ) * ((u ^ 2)⁻¹) := by
    have h := Complex.mul_conj' (u ^ 2)
    rw [norm_pow, hU, ← Complex.ofReal_pow] at h
    have eX : ((t ^ 2) ^ 2 : ℝ) = t ^ 4 := by ring
    rw [eX] at h
    have hu2 : (u ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hu0
    have hcc : (starRingEnd ℂ) (u ^ 2)
        = ((u ^ 2)⁻¹) * ((u ^ 2) * (starRingEnd ℂ) (u ^ 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hu2, one_mul]
    rw [hcc, h]
    ring
  have h4 : ((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)
      = ((((t ^ 4)⁻¹ : ℝ)) : ℂ) * (starRingEnd ℂ) (u ^ 2 * m u) := by
    have h5 : ((((t ^ 4)⁻¹ : ℝ)) : ℂ) * ((t ^ 4 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht4, Complex.ofReal_one]
    calc ((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)
        = 1 * (((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)) := by ring
      _ = (((((t ^ 4)⁻¹ : ℝ)) : ℂ) * ((t ^ 4 : ℝ) : ℂ)) *
          (((u ^ 2)⁻¹) * (starRingEnd ℂ) (m u)) := by rw [h5]
      _ = _ := by rw [map_mul, h3]; ring
  have h4' : (-(((u ^ 2))⁻¹)) * (starRingEnd ℂ) (m u)
      = -(((((t ^ 4)⁻¹ : ℝ)) : ℂ) * (starRingEnd ℂ) (u ^ 2 * m u)) := by
    rw [neg_mul, h4]
  have h7 : ∀ (s : ℝ) (z : ℂ), (((s : ℝ) : ℂ) * z).re = s * z.re := by
    intro s z
    simp [Complex.mul_re]
  have hcross : ((-(((u ^ 2))⁻¹)) * (starRingEnd ℂ) (m u)).re
      = -(t⁻¹ ^ 4) * (((u ^ 2 * m u)).re) := by
    have eS : ((((t ^ 4)⁻¹ : ℝ))) = t⁻¹ ^ 4 := by rw [inv_pow]
    rw [h4', Complex.neg_re, h7, Complex.conj_re, eS, neg_mul]
  have hA2 : ‖(((u ^ 2))⁻¹)‖ ^ 2 = t⁻¹ ^ 4 := by
    rw [norm_inv, norm_pow, hU]
    simp only [inv_pow]
    have eX : ((t ^ 2) ^ 2 : ℝ) = t ^ 4 := by ring
    rw [eX]
  have hAsq : Complex.normSq (-(((u ^ 2))⁻¹)) = t⁻¹ ^ 4 := by
    rw [Complex.normSq_neg, Complex.normSq_eq_norm_sq]
    exact hA2
  have hcsq : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
  have hcross2 : (-(((u ^ 2))⁻¹) *
      (starRingEnd ℂ) (c + (m u - c))).re
      = -(t⁻¹ ^ 4) * (((u ^ 2 * m u)).re) := by
    have hce : c + (m u - c) = m u := add_sub_cancel c (m u)
    rw [hce]
    exact hcross
  have hconj_e : (c * (starRingEnd ℂ) (m u - c)).re
      = (((starRingEnd ℂ) c * (m u - c))).re :=
    hconj c _
  have hns : Complex.normSq (-(((u ^ 2))⁻¹) + m u)
      = t⁻¹ ^ 4 + (‖c‖ ^ 2 + 2 * ((((starRingEnd ℂ) c * (m u - c))).re) +
        (Complex.normSq (m u - c) +
          2 * (-(t⁻¹ ^ 4) * (((u ^ 2 * m u)).re)))) := by
    have e1 : (-(((u ^ 2))⁻¹) + m u)
        = (-(((u ^ 2))⁻¹)) + (c + (m u - c)) := by
      rw [add_sub_cancel]
    rw [e1, Complex.normSq_add, Complex.normSq_add, hAsq, hcsq, hcross2,
      hconj_e]
    ring
  have hle : t⁻¹ ^ 4 + ‖c‖ ^ 2
      + 2 * (((starRingEnd ℂ) c * (m u - c)).re)
      - 2 * t⁻¹ ^ 4 * (((u ^ 2 * m u)).re)
      ≤ Complex.normSq (-(((u ^ 2))⁻¹) + m u) := by
    rw [hns]
    have hnn : 0 ≤ Complex.normSq (m u - c) := Complex.normSq_nonneg _
    linarith
  rwa [Complex.normSq_eq_norm_sq] at hle

theorem koebe_circle_integral_lower
    (m : ℂ → ℂ) (c : ℂ) (t : ℝ)
    (hm : DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1))
    (hm0 : m 0 = c)
    (ht0 : 0 < t) (ht1 : t < 1) :
    2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2) ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖-(((circleMap 0 t θ) ^ 2)⁻¹) + m (circleMap 0 t θ)‖ ^ 2 := by
  have htne : t ≠ 0 := ne_of_gt ht0
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 t θ‖ = t := by
    intro θ
    rw [norm_circleMap_zero, abs_of_pos ht0]
  have hmem : ∀ θ : ℝ, circleMap 0 t θ ∈ Metric.ball (0 : ℂ) 1 := by
    intro θ
    rw [Metric.mem_ball, dist_zero_right, hnorm θ]
    exact ht1
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2π : (2 * Real.pi) ≠ 0 := ne_of_gt hpos
  have hmw_cont : ContinuousOn (fun θ : ℝ => m (circleMap 0 t θ))
      (Set.uIcc 0 (2 * Real.pi)) := by
    have hmaps : Set.MapsTo (circleMap 0 t) (Set.uIcc 0 (2 * Real.pi))
        (Metric.ball (0 : ℂ) 1) :=
      fun θ _ => hmem θ
    have h := (hm.continuousOn).comp (continuous_circleMap 0 t).continuousOn
      hmaps
    exact h.congr (fun θ _ => rfl)
  have hsqc : ContinuousOn (fun θ : ℝ => (circleMap 0 t θ) ^ 2)
      (Set.uIcc 0 (2 * Real.pi)) :=
    ((continuous_circleMap 0 t).continuousOn.mul
      (continuous_circleMap 0 t).continuousOn).congr
      (fun θ _ => pow_two _)
  have hconst_c : ContinuousOn (fun _ : ℝ => c) (Set.uIcc 0 (2 * Real.pi)) :=
    continuous_const.continuousOn
  have hsubc : ContinuousOn (fun θ : ℝ => m (circleMap 0 t θ) - c)
      (Set.uIcc 0 (2 * Real.pi)) :=
    (hmw_cont.sub hconst_c).congr (fun θ _ => rfl)
  have hRe1c : ContinuousOn
      (fun θ : ℝ => ((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have h := (Complex.continuous_re.continuousOn).comp
      (hsubc.const_mul ((starRingEnd ℂ) c)) (Set.mapsTo_univ _ _)
    exact h.congr (fun θ _ => rfl)
  have hF2c : ContinuousOn
      (fun θ : ℝ => (circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))
      (Set.uIcc 0 (2 * Real.pi)) :=
    (hsqc.mul hmw_cont).congr (fun θ _ => rfl)
  have hRe2c : ContinuousOn
      (fun θ : ℝ => (((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have h := (Complex.continuous_re.continuousOn).comp hF2c
      (Set.mapsTo_univ _ _)
    exact h.congr (fun θ _ => rfl)
  have hAc : ContinuousOn (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have hne : ∀ θ ∈ Set.uIcc 0 (2 * Real.pi),
        ((circleMap 0 t θ) ^ 2) ≠ 0 := by
      intro θ _
      have h0' : circleMap 0 t θ ≠ 0 := by
        intro hcon
        apply htne
        rw [← hnorm θ, hcon, norm_zero]
      exact pow_ne_zero 2 h0'
    have h := hsqc.inv₀ hne
    have h2 := h.neg
    exact h2.congr (fun θ _ => rfl)
  have hsumc : ContinuousOn
      (fun θ : ℝ => -(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ))
      (Set.uIcc 0 (2 * Real.pi)) :=
    (hAc.add hmw_cont).congr (fun θ _ => rfl)
  have hFc : ContinuousOn
      (fun θ : ℝ => ‖-(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ)‖ ^ 2)
      (Set.uIcc 0 (2 * Real.pi)) := by
    have h := (hsumc.norm).mul (hsumc.norm)
    exact h.congr (fun θ _ => pow_two _)
  have hint_F : IntervalIntegrable
      (fun θ : ℝ => ‖-(((circleMap 0 t θ) ^ 2))⁻¹ + m (circleMap 0 t θ)‖ ^ 2)
      volume 0 (2 * Real.pi) := hFc.intervalIntegrable
  have hint_m : IntervalIntegrable (fun θ : ℝ => m (circleMap 0 t θ))
      volume 0 (2 * Real.pi) := hmw_cont.intervalIntegrable
  have hint_c : IntervalIntegrable (fun _ : ℝ => c) volume 0 (2 * Real.pi) :=
    hconst_c.intervalIntegrable
  have hint_Re1 : IntervalIntegrable
      (fun θ : ℝ => ((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re)
      volume 0 (2 * Real.pi) := hRe1c.intervalIntegrable
  have hint_Re2 : IntervalIntegrable
      (fun θ : ℝ => (((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)
      volume 0 (2 * Real.pi) := hRe2c.intervalIntegrable
  have hint_F2 : IntervalIntegrable
      (fun θ : ℝ => (circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))
      volume 0 (2 * Real.pi) := hF2c.intervalIntegrable
  have hint_sub : IntervalIntegrable
      (fun θ : ℝ => (starRingEnd ℂ) c * (m (circleMap 0 t θ) - c))
      volume 0 (2 * Real.pi) :=
    (hsubc.const_mul _).intervalIntegrable
  have hsub : closure (Metric.ball (0 : ℂ) |t|) ⊆ Metric.ball (0 : ℂ) 1 := by
    have h1 : closure (Metric.ball (0 : ℂ) |t|)
        ⊆ Metric.closedBall (0 : ℂ) |t| :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    have h2 : Metric.closedBall (0 : ℂ) |t| ⊆ Metric.ball (0 : ℂ) 1 := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      rw [abs_of_pos ht0] at hz
      linarith
    exact h1.trans h2
  have hdiff_m : DiffContOnCl ℂ m (Metric.ball (0 : ℂ) |t|) :=
    (hm.mono hsub).diffContOnCl
  have hF2 : DifferentiableOn ℂ (fun z => z ^ 2 * m z)
      (Metric.ball (0 : ℂ) 1) :=
    ((DifferentiableOn.pow differentiableOn_id 2).mono
      (Set.subset_univ _)).mul hm
  have hdiff_F2 : DiffContOnCl ℂ (fun z => z ^ 2 * m z)
      (Metric.ball (0 : ℂ) |t|) :=
    (hF2.mono hsub).diffContOnCl
  have hmean_m : (∫ θ in (0 : ℝ)..(2 * Real.pi), m (circleMap 0 t θ))
      = (2 * Real.pi) • c := by
    have h0 := DiffContOnCl.circleAverage hdiff_m
    rw [Real.circleAverage_def, hm0] at h0
    have h := congrArg ((2 * Real.pi) • ·) h0
    rwa [smul_inv_smul₀ h2π] at h
  have hmean_F2 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ)) = 0 := by
    have h0 := DiffContOnCl.circleAverage hdiff_F2
    rw [Real.circleAverage_def] at h0
    have hF200 : (0 : ℂ) ^ 2 * m 0 = 0 := by simp
    rw [hF200] at h0
    have h := congrArg ((2 * Real.pi) • ·) h0
    rwa [smul_inv_smul₀ h2π, smul_zero] at h
  have hRe1 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re)) = 0 := by
    simp only [← Complex.reCLM_apply]
    rw [ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint_sub,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hint_m hint_c, hmean_m,
      intervalIntegral.integral_const]
    simp
  have hRe2 : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)) = 0 := by
    simp only [← Complex.reCLM_apply]
    rw [ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint_F2,
      hmean_F2, map_zero]
  have hint_2Re1 : IntervalIntegrable
      (fun θ : ℝ => 2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re))
      volume 0 (2 * Real.pi) :=
    (hRe1c.const_mul 2).intervalIntegrable
  have hint_K : IntervalIntegrable (fun _ : ℝ => t⁻¹ ^ 4 + ‖c‖ ^ 2)
      volume 0 (2 * Real.pi) :=
    continuous_const.continuousOn.intervalIntegrable
  have hint_L1 : IntervalIntegrable
      (fun θ : ℝ => t⁻¹ ^ 4 + ‖c‖ ^ 2 +
        2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re))
      volume 0 (2 * Real.pi) :=
    hint_K.add hint_2Re1
  have hint_2tRe2 : IntervalIntegrable
      (fun θ : ℝ => 2 * t⁻¹ ^ 4 *
        ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re))
      volume 0 (2 * Real.pi) :=
    (hRe2c.const_mul (2 * t⁻¹ ^ 4)).intervalIntegrable
  have hint_L : IntervalIntegrable
      (fun θ : ℝ => t⁻¹ ^ 4 + ‖c‖ ^ 2 +
        2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re) -
        2 * t⁻¹ ^ 4 * ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re))
      volume 0 (2 * Real.pi) :=
    hint_L1.sub hint_2tRe2
  have hLval : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (t⁻¹ ^ 4 + ‖c‖ ^ 2 +
        2 * (((starRingEnd ℂ) c * (m (circleMap 0 t θ) - c)).re) -
        2 * t⁻¹ ^ 4 * ((((circleMap 0 t θ) ^ 2 * m (circleMap 0 t θ))).re)))
      = 2 * Real.pi * (t⁻¹ ^ 4 + ‖c‖ ^ 2) := by
    rw [intervalIntegral.integral_sub hint_L1 hint_2tRe2,
      intervalIntegral.integral_add hint_K hint_2Re1,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hRe1, hRe2, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hmono := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    hint_L hint_F (fun x _ => koebe_pointwise_lower m c t (circleMap 0 t x) ht0
      (hnorm x))
  rw [hLval] at hmono
  exact hmono

end Complex.KoebeQuarterWanted
end
