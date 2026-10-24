/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/HartogsSeparateAnalyticity.lean -/


import sympy.atlas.Analysis.Complex.HartogsSeparateAnalyticity

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord


namespace MathlibExtTest.Analysis.Complex.HartogsSeparateAnalyticity

open MathlibExt.Analysis.Complex.HartogsWanted Metric

-- A nonconstant polynomial satisfies the circle sub-mean inequality for `log⁺ ‖f‖`.
example :
  Real.posLog ‖(2 : ℂ)‖ ≤
      Real.circleAverage (fun z : ℂ ↦ Real.posLog ‖z + 2‖) 0 1 := by
  simpa using hartogs_posLog_norm_le_circleAverage (c := 0) (R := 1)
    (f := fun z : ℂ ↦ z + 2) (by norm_num) (by fun_prop)

-- Multiplication satisfies the bounded bidisc form of Osgood's lemma.
example : DifferentiableAt ℂ (Function.uncurry fun z w : ℂ ↦ z * w) (0, 0) := by
  apply differentiableAt_uncurry_of_separately_differentiable_of_bounded (M := 1)
  · intro w
    exact differentiable_id.mul_const w
  · intro z
    exact (differentiable_const z).mul differentiable_id
  · intro z hz w hw
    rw [norm_mul]
    have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall] using hz
    have hw' : ‖w‖ ≤ 1 := by simpa [mem_closedBall] using hw
    calc
      ‖z‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hz' (norm_nonneg w)
      _ = ‖w‖ := one_mul _
      _ ≤ 1 := hw'

-- The Osgood lemma treats the first variable as a genuine normed-space block.
example : DifferentiableAt ℂ
    (Function.uncurry fun z : ℂ × ℂ ↦ fun w : ℂ ↦ z.1 + w) (0, 0) := by
  apply differentiableAt_uncurry_of_separately_differentiable_of_bounded (M := 2)
  · intro w
    fun_prop
  · intro z
    fun_prop
  · intro z hz w hw
    have hz' : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
    have hz₁ : ‖z.1‖ ≤ 1 := by
      rw [Prod.norm_def] at hz'
      exact (le_max_left _ _).trans hz'
    have hw' : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hw
    exact (norm_add_le _ _).trans (by linarith)

-- The neighborhood form handles translated products and a non-scalar first block.
example : DifferentiableAt ℂ
    (Function.uncurry fun z : ℂ × ℂ ↦ fun w : ℂ ↦
      (z.1 - 1) + (w - 2)) ((1, 0), 2) := by
  apply differentiableAt_uncurry_of_separately_differentiable_of_locally_bounded
    (U := ball ((1, 0) : ℂ × ℂ) 1) (V := ball (2 : ℂ) 1) (M := 2)
    isOpen_ball isOpen_ball
  · intro w
    fun_prop
  · intro z
    fun_prop
  · intro z hz w hw
    have hz' : ‖z.1 - 1‖ < 1 := by
      calc
        ‖z.1 - 1‖ ≤ ‖z - ((1, 0) : ℂ × ℂ)‖ := by
          simpa using norm_fst_le (z - ((1, 0) : ℂ × ℂ))
        _ = dist z (1, 0) := by rw [dist_eq_norm]
        _ < 1 := mem_ball.1 hz
    have hw' : ‖w - 2‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
    exact (norm_add_le _ _).trans (by linarith)
  · simp
  · simp

-- Cauchy coefficients are holomorphic in a genuine finite-dimensional parameter block.
example : DifferentiableOn ℂ
    (fun z : Fin 2 → ℂ ↦
      (cauchyPowerSeries (fun w ↦ z 0 * w + z 1) 0 (1 / 2) 1) (fun _ ↦ 1))
    (ball 0 (1 / 2)) := by
  apply differentiableOn_cauchyCoefficient_of_separately_differentiable_of_bounded
    (A := 1) (B := 1) (M := 2) (by norm_num) (by norm_num)
  · intro w
    fun_prop
  · intro z
    fun_prop
  · intro z hz w hw
    have hz' (i : Fin 2) : ‖z i‖ ≤ 1 := by
      have hi := (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).1
        (mem_closedBall.1 hz) i
      simpa [dist_zero_right] using hi
    have hw' : ‖w‖ ≤ 1 := by simpa [mem_closedBall] using hw
    calc
      ‖z 0 * w + z 1‖ ≤ ‖z 0‖ * ‖w‖ + ‖z 1‖ := by
        simpa [norm_mul] using norm_add_le (z 0 * w) (z 1)
      _ ≤ 1 * 1 + 1 := by gcongr <;> exact hz' _
      _ = 2 := by norm_num

-- The coefficient estimate detects the sharp unit-circle bound for `z ↦ z²`.
example : ‖(cauchyPowerSeries (fun z : ℂ ↦ z ^ 2) 0 1).coeff 2‖ ≤ 1 := by
  simpa using norm_cauchyCoefficient_le (c := 0) (R := 1) (M := 1)
    (f := fun z : ℂ ↦ z ^ 2) (by norm_num) (by fun_prop)
    (by
      intro z hz
      have hz' : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
      simp [norm_pow, hz'])
    2

-- The iterated sub-mean theorem gives a nonconstant solid-disc inequality.
example :
    (MeasureTheory.volume (closedBall (0 : ℂ) 1)).toReal ^ (1 : ℕ) *
        Real.posLog ‖(2 : ℂ)‖ ≤
      hartogsPolydiscIntegral
        (fun x : Fin 1 → ℂ ↦ Real.posLog ‖x 0 + 2‖) 0 1 := by
  have h := hartogsPolydisc_submean
    (n := 1) (u := fun x : Fin 1 → ℂ ↦ Real.posLog ‖x 0 + 2‖)
    (c := 0) (R := 1) (by fun_prop) (by norm_num)
    (by
      intro x _hx i r hr
      fin_cases i
      simpa using hartogs_posLog_norm_le_circleAverage
        (c := x 0) (R := r) (f := fun z : ℂ ↦ z + 2) hr.1 (by fun_prop))
  simpa using h

-- Hartogs' lemma upgrades pointwise geometric decay to uniform decay on a smaller polydisc.
example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ x ∈ closedBall (0 : Fin 1 → ℂ) (1 / 4 : ℝ),
      (1 / 2 : ℝ) ^ k ≤ ε := by
  apply hartogs_eventually_uniform_of_submean
    (n := 1) (u := fun k (_x : Fin 1 → ℂ) ↦ (1 / 2 : ℝ) ^ k)
    (c := 0) (R := 1) (C := 1) (by norm_num)
  · intro k
    fun_prop
  · intro k x hx
    positivity
  · norm_num
  · intro k x hx
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · intro x hx
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · intro k x hx i r hr hincl
    simp only [Real.circleAverage_const]
    rfl
  · exact hε

-- The final theorem handles a polynomial depending on two Euclidean coordinates.
example : Differentiable ℂ
    (fun x : EuclideanSpace ℂ (Fin 2) ↦
      WithLp.ofLp x 0 * WithLp.ofLp x 1) := by
  apply hartogs_separate_analyticity
  intro x i
  fin_cases i
  · simp
  · simp only [Fin.isValue, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
      Function.update_of_ne, Function.update_self]
    fun_prop

end MathlibExtTest.Analysis.Complex.HartogsSeparateAnalyticity
