/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part10
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem auxAr_deriv_tendstoUniformlyOn_Ioo {a b : ℝ} (ha0 : 0 < a)
    (hab : a < b) (hb1 : b < Real.pi / 2) :
    TendstoUniformlyOn (fun r x => auxAr_deriv r x) auxA_deriv_lim
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (Set.Ioo a b) := by
  have ha_pi : a < Real.pi := by linarith [Real.pi_pos]
  have hsin_a_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 ha_pi
  have hsin_a_nn : (0 : ℝ) ≤ Real.sin a := le_of_lt hsin_a_pos
  set m : ℝ := 2 * Real.sin a ^ 2 with hmdef
  have hmpos : 0 < m := by
    unfold m
    have hsq : 0 < Real.sin a ^ 2 := pow_pos hsin_a_pos 2
    linarith
  set M : ℝ := 5 with hMdef
  have hsub : Set.Icc m M ⊆ {0}ᶜ := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hy1 : m ≤ y := (Set.mem_Icc.mp hy).1
    have hpos : (0 : ℝ) < y := lt_of_lt_of_le hmpos hy1
    exact ne_of_gt hpos
  have hcont : ContinuousOn Real.log (Set.Icc m M) :=
    Real.continuousOn_log.mono hsub
  have hunif : UniformContinuousOn Real.log (Set.Icc m M) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp hunif) ε hε
  have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hIooW : Set.Ioo 0 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin_of_mem_nhds hIoo
  have hIioW : Set.Iio (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    self_mem_nhdsWithin
  have hHalf : Set.Ioo (1 / 2 : ℝ) 2 ∈ nhds (1 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hHalfW : Set.Ioo (1 / 2 : ℝ) 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin_of_mem_nhds hHalf
  have htendsto_id : Filter.Tendsto id (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (1 : ℝ)) :=
    continuousWithinAt_id.tendsto
  have hcont_abs : ContinuousAt (fun r : ℝ => |1 - r|) 1 := by fun_prop
  have htendsto_abs : Filter.Tendsto (fun r : ℝ => |1 - r|)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
    have h : Filter.Tendsto (fun r : ℝ => |1 - r|)
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds |1 - 1|) :=
      hcont_abs.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have hmem_delta : Set.Iio (δ / 5) ∈ nhds (0 : ℝ) := by
    apply Iio_mem_nhds
    linarith
  have hdelta : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), |1 - r| < δ / 5 :=
    htendsto_abs.eventually hmem_delta
  filter_upwards [hIooW, hIioW, hHalfW, hdelta] with r hrIoo hrIio hrHalf hrδ x hx
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (Set.mem_Ioo.mp hrIoo).1
  have hr1 : r < 1 := hrIio
  have hrhalf : (1 / 2 : ℝ) < r := (Set.mem_Ioo.mp hrHalf).1
  have hrhalf_le : (1 / 2 : ℝ) ≤ r := le_of_lt hrhalf
  have hr_le1 : r ≤ 1 := le_of_lt hr1
  have hclosed : auxAr_deriv r x = -Real.log ((1 - r) ^ 2 + 4 * r * Real.sin x ^ 2) := by
    unfold auxAr_deriv
    exact auxAr_deriv_eq_log hr0 hr1 x
  have hx1 : a < x := (Set.mem_Ioo.mp hx).1
  have hx2 : x < b := (Set.mem_Ioo.mp hx).2
  have hsin_ge : Real.sin a ≤ Real.sin x := aux_sin_ge_sin_a ha0 hb1 hx
  have hsin_x_pos : 0 < Real.sin x := by
    have hx0 : (0 : ℝ) < x := lt_trans ha0 hx1
    have hxpi : x < Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hsin_x_nn : (0 : ℝ) ≤ Real.sin x := le_of_lt hsin_x_pos
  have hsq_ge : Real.sin a ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ hsin_a_nn hsin_ge 2
  have hsq_x_nn : (0 : ℝ) ≤ Real.sin x ^ 2 := sq_nonneg _
  have hsq_x_le1 : Real.sin x ^ 2 ≤ 1 := by
    have h1 := Real.abs_sin_le_one x
    have h2 := abs_le.mp h1
    nlinarith [h2.1, h2.2, sq_nonneg (Real.sin x)]
  have hsq_a_le1 : Real.sin a ^ 2 ≤ 1 := by
    have h1 := Real.abs_sin_le_one a
    have h2 := abs_le.mp h1
    nlinarith [h2.1, h2.2, sq_nonneg (Real.sin a)]
  have h1r_nn : (0 : ℝ) ≤ 1 - r := by linarith
  have h1r_le1 : 1 - r ≤ 1 := by linarith
  have h1r_sq_le1 : (1 - r) ^ 2 ≤ 1 := pow_le_one₀ h1r_nn h1r_le1
  have h1r_sq_nn : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
  set u : ℝ := 4 * Real.sin x ^ 2 with hudef
  set ur : ℝ := (1 - r) ^ 2 + 4 * r * Real.sin x ^ 2 with hurdef
  have hu_mem : u ∈ Set.Icc m M := by
    constructor
    · unfold m u
      nlinarith [hsq_ge, hsq_x_nn, hsq_a_le1]
    · unfold M u
      nlinarith [hsq_x_le1, hsq_x_nn]
  have hur_mem : ur ∈ Set.Icc m M := by
    constructor
    · unfold m ur
      have h1 : (0 : ℝ) ≤ (1 - r) ^ 2 := h1r_sq_nn
      have h2 : 2 * Real.sin a ^ 2 ≤ 4 * r * Real.sin x ^ 2 := by
        have hmul : (1 / 2 : ℝ) * Real.sin a ^ 2 ≤ r * Real.sin x ^ 2 := by
          apply mul_le_mul hrhalf_le hsq_ge (sq_nonneg _) (by linarith)
        linarith
      linarith
    · unfold M ur
      have h1 : (1 - r) ^ 2 ≤ 1 := h1r_sq_le1
      have h2 : 4 * r * Real.sin x ^ 2 ≤ 4 := by
        have hr_nn : (0 : ℝ) ≤ r := hr0
        nlinarith [hr_le1, hsq_x_le1, hsq_x_nn, hr_nn, sq_nonneg r]
      linarith
  have hdiff_eq : u - ur = (1 - r) * (4 * Real.sin x ^ 2 - (1 - r)) := by
    unfold u ur
    ring
  have hfactor_le5 : |4 * Real.sin x ^ 2 - (1 - r)| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith [hsq_x_nn, hsq_x_le1, h1r_nn, h1r_le1]
  have hdiff_le : |u - ur| ≤ 5 * |1 - r| := by
    rw [hdiff_eq, abs_mul]
    calc |1 - r| * |4 * Real.sin x ^ 2 - (1 - r)|
        ≤ |1 - r| * 5 := mul_le_mul_of_nonneg_left hfactor_le5 (abs_nonneg _)
      _ = 5 * |1 - r| := by ring
  have hdist_lt : dist u ur < δ := by
    rw [Real.dist_eq]
    calc |u - ur| ≤ 5 * |1 - r| := hdiff_le
      _ < 5 * (δ / 5) := by
          apply mul_lt_mul_of_pos_left hrδ (by norm_num)
      _ = δ := by ring
  have hlog_dist : dist (Real.log u) (Real.log ur) < ε := hδ _ hu_mem _ hur_mem hdist_lt
  have hgoal_eq : dist (auxA_deriv_lim x) (auxAr_deriv r x) =
      dist (Real.log u) (Real.log ur) := by
    rw [hclosed]
    unfold auxA_deriv_lim
    rw [Real.dist_eq, Real.dist_eq]
    have heq : (-Real.log u) - (-Real.log ur) =
        -(Real.log u - Real.log ur) := by ring
    rw [heq, abs_neg]
  rw [hgoal_eq]
  exact hlog_dist

theorem auxA_fourier_hasDerivAt {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt auxA_fourier (auxA_deriv_lim x₀) x₀ := by
  have hx0_pos : 0 < x₀ := (Set.mem_Ioo.mp hx₀).1
  have hx0_lt : x₀ < Real.pi / 2 := (Set.mem_Ioo.mp hx₀).2
  set a : ℝ := x₀ / 2 with hadef
  set b : ℝ := (x₀ + Real.pi / 2) / 2 with hbdef
  have ha0 : 0 < a := by unfold a; linarith
  have hab : a < b := by unfold a b; linarith [Real.pi_pos]
  have hb1 : b < Real.pi / 2 := by unfold b; linarith
  have hax : a < x₀ := by unfold a; linarith
  have hxb : x₀ < b := by unfold b; linarith
  have hxmem : x₀ ∈ Set.Ioo a b := ⟨hax, hxb⟩
  have hf' : TendstoUniformlyOn (fun r x => auxAr_deriv r x) auxA_deriv_lim
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (Set.Ioo a b) :=
    auxAr_deriv_tendstoUniformlyOn_Ioo ha0 hab hb1
  have hf : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ x : ℝ, x ∈ Set.Ioo a b → HasDerivAt (auxAr r) (auxAr_deriv r x) x := by
    have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    have hIooW : Set.Ioo 0 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
      mem_nhdsWithin_of_mem_nhds hIoo
    have hIioW : Set.Iio (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
      self_mem_nhdsWithin
    filter_upwards [hIooW, hIioW] with r hrIoo hrIio x hx
    have hr0 : (0 : ℝ) ≤ r := le_of_lt (Set.mem_Ioo.mp hrIoo).1
    have hr1 : r < 1 := hrIio
    exact auxAr_hasDerivAt hr0 hr1 x
  have hfg : ∀ x : ℝ, x ∈ Set.Ioo a b →
      Filter.Tendsto (fun r => auxAr r x) (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (auxA_fourier x)) :=
    fun x _ => auxAr_tendsto x
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hf' hf hfg hxmem

theorem aux_logterm_tendsto_nhdsGT :
    Filter.Tendsto chapter9Entry20LogTerm (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have ha : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcont : Continuous (fun x : ℝ => x ^ 2 / 2 * Real.log 2) :=
      ((continuous_id'.pow 2).div_const 2).mul continuous_const
    have h : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((0 : ℝ) ^ 2 / 2 * Real.log 2)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hb : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (show (0 : ℝ) < 2 by norm_num)
    simp only [Real.rpow_two] at h
    have h2 := h.div_const (2 : ℝ)
    have heq : (fun x : ℝ => x ^ 2 / 2 * Real.log x) =
        (fun x : ℝ => Real.log x * x ^ 2 / 2) := by
      funext x
      ring
    rw [heq]
    simpa using h2
  have hc : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log (Real.sinc x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc0 : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hcont : Continuous (fun x : ℝ => x ^ 2 / 2) :=
        (continuous_id'.pow 2).div_const 2
      have h : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((0 : ℝ) ^ 2 / 2)) :=
        (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    have hc1 : Filter.Tendsto (fun x : ℝ => Real.log (Real.sinc x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hsinc : Filter.Tendsto Real.sinc
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
        have h : Filter.Tendsto Real.sinc (nhds (0 : ℝ)) (nhds (Real.sinc 0)) :=
          Real.continuous_sinc.tendsto 0
        rw [Real.sinc_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hlog : Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds 0) := by
        have h : Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds (Real.log 1)) :=
          (Real.continuousAt_log one_ne_zero).tendsto
        simpa using h
      exact hlog.comp hsinc
    have hmul := hc0.mul hc1
    simpa using hmul
  have hsum : Filter.Tendsto
      (fun x : ℝ => (x ^ 2 / 2 * Real.log 2 + x ^ 2 / 2 * Real.log x) +
        x ^ 2 / 2 * Real.log (Real.sinc x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (ha.add hb).add hc
    simpa using h
  have heq : chapter9Entry20LogTerm =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun x : ℝ => (x ^ 2 / 2 * Real.log 2 + x ^ 2 / 2 * Real.log x) +
        x ^ 2 / 2 * Real.log (Real.sinc x)) := by
    have hlt : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x < Real.pi :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpi)
    have hsinc_ne : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), Real.sinc x ≠ 0 := by
      have h : ∀ᶠ x in nhds (0 : ℝ), Real.sinc x ≠ 0 := by
        have hs : Filter.Tendsto Real.sinc (nhds (0 : ℝ)) (nhds 1) := by
          have h : Filter.Tendsto Real.sinc (nhds (0 : ℝ)) (nhds (Real.sinc 0)) :=
            Real.continuous_sinc.tendsto 0
          rwa [Real.sinc_zero] at h
        exact hs.eventually (eventually_ne_nhds one_ne_zero)
      exact eventually_nhdsWithin_of_eventually_nhds h
    filter_upwards [self_mem_nhdsWithin, hlt, hsinc_ne] with x hx0 hxpi hxne
    have hxpos : (0 : ℝ) < x := hx0
    have hxne0 : x ≠ 0 := ne_of_gt hxpos
    have hsin_pos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hxpos hxpi
    have h2sin_pos : (0 : ℝ) < 2 * Real.sin x := by linarith
    have habs : |2 * Real.sin x| = 2 * Real.sin x := abs_of_pos h2sin_pos
    have hsinc_eq : x * Real.sinc x = Real.sin x := by
      rw [Real.sinc_of_ne_zero hxne0]
      field_simp
    have hx_sinc_ne : x * Real.sinc x ≠ 0 := mul_ne_zero hxne0 hxne
    have e : (2 : ℝ) * Real.sin x = 2 * (x * Real.sinc x) := by rw [hsinc_eq]
    have hsplit : Real.log (2 * Real.sin x) =
        Real.log 2 + (Real.log x + Real.log (Real.sinc x)) := by
      rw [e, Real.log_mul (by norm_num) hx_sinc_ne, Real.log_mul hxne0 hxne]
    have hif : chapter9Entry20LogTerm x =
        x ^ 2 / 2 * (Real.log 2 + (Real.log x + Real.log (Real.sinc x))) := by
      unfold chapter9Entry20LogTerm
      simp only [hxne0, ite_false, habs, hsplit]
    rw [hif]
    ring
  exact Filter.Tendsto.congr' heq.symm hsum

theorem aux_sin_pos_of_Ioo {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin x₀ := by
  have hx0_pos : 0 < x₀ := (Set.mem_Ioo.mp hx₀).1
  have hx0_lt : x₀ < Real.pi := by
    have h := (Set.mem_Ioo.mp hx₀).2
    linarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi hx0_pos hx0_lt

theorem aux_logterm_eventuallyEq {x₀ : ℝ} (hx0_ne : x₀ ≠ 0)
    (h2sin_pos : (0 : ℝ) < 2 * Real.sin x₀) :
    chapter9Entry20LogTerm =ᶠ[nhds x₀]
      fun x => x ^ 2 / 2 * Real.log (2 * Real.sin x) := by
  have hne : ∀ᶠ x in nhds x₀, x ≠ 0 := eventually_ne_nhds hx0_ne
  have hpos : ∀ᶠ x in nhds x₀, (0 : ℝ) < 2 * Real.sin x := by
    have hsin : ContinuousAt Real.sin x₀ := Real.continuous_sin.continuousAt
    have hcont : ContinuousAt (fun x : ℝ => 2 * Real.sin x) x₀ :=
      hsin.const_mul 2
    exact hcont.tendsto.eventually (eventually_gt_nhds h2sin_pos)
  filter_upwards [hne, hpos] with x hxne hxpos
  unfold chapter9Entry20LogTerm
  simp only [hxne, ite_false, abs_of_pos hxpos]

theorem aux_logterm_smooth_hasDerivAt {x₀ : ℝ}
    (h2sin_ne : (2 : ℝ) * Real.sin x₀ ≠ 0) :
    HasDerivAt (fun x => x ^ 2 / 2 * Real.log (2 * Real.sin x))
      (x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀))
      x₀ := by
  have hsin_ne : Real.sin x₀ ≠ 0 := fun h => h2sin_ne (by rw [h, mul_zero])
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x₀ x₀ := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x₀) x₀ := by
      have h := hasDerivAt_pow 2 x₀
      simpa [pow_one] using h
    have hdiv := hpow.div_const (2 : ℝ)
    have heq : (2 * x₀) / 2 = x₀ := by ring
    rw [heq] at hdiv
    exact hdiv
  have h2 : HasDerivAt (fun x : ℝ => 2 * Real.sin x) (2 * Real.cos x₀) x₀ :=
    (Real.hasDerivAt_sin x₀).const_mul 2
  have h3 : HasDerivAt (fun x : ℝ => Real.log (2 * Real.sin x))
      ((2 * Real.cos x₀) / (2 * Real.sin x₀)) x₀ := h2.log h2sin_ne
  have hmul : HasDerivAt (fun x : ℝ => x ^ 2 / 2 * Real.log (2 * Real.sin x))
      (x₀ * Real.log (2 * Real.sin x₀) +
        x₀ ^ 2 / 2 * ((2 * Real.cos x₀) / (2 * Real.sin x₀))) x₀ :=
    h1.mul h3
  have heq : x₀ * Real.log (2 * Real.sin x₀) +
      x₀ ^ 2 / 2 * ((2 * Real.cos x₀) / (2 * Real.sin x₀)) =
      x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀) := by
    congr 1
    congr 1
    field_simp
  rw [heq] at hmul
  exact hmul

theorem aux_logterm_hasDerivAt {x₀ : ℝ} (hx0_ne : x₀ ≠ 0)
    (h2sin_pos : (0 : ℝ) < 2 * Real.sin x₀) :
    HasDerivAt chapter9Entry20LogTerm
      (x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀))
      x₀ :=
  (aux_logterm_smooth_hasDerivAt (ne_of_gt h2sin_pos)).congr_of_eventuallyEq
    (aux_logterm_eventuallyEq hx0_ne h2sin_pos)

theorem auxA_deriv_lim_eq (x₀ : ℝ) :
    auxA_deriv_lim x₀ = -2 * Real.log (2 * Real.sin x₀) := by
  unfold auxA_deriv_lim
  have hsq : (4 : ℝ) * Real.sin x₀ ^ 2 = (2 * Real.sin x₀) ^ 2 := by ring
  rw [hsq, Real.log_pow]
  ring

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
