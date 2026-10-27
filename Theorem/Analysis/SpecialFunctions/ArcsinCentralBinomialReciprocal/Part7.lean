import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Def.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part8


namespace MetaMathlibExt

theorem hasDerivAt_Jfun (y : ℝ) (hy : |y| < 1) : HasDerivAt Jfun 0 y := by
  have hpos : (0:ℝ) < 1 - y ^ 2 := hpos_of_mem y hy
  have hne : (1:ℝ) - y ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - y ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hsq : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  have hK : HasDerivAt (fun z => Dfun z - H1fun z) (S2fun y - H2fun y) y :=
    (hasDerivAt_Dfun y hy).sub (hasDerivAt_H1 y hy)
  have h_inner : HasDerivAt (fun z => (1:ℝ) - z ^ 2) (-2 * y) y := by
    have h1 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
      have h := hasDerivAt_pow 2 y
      refine h.congr_deriv ?_
      push_cast
      ring
    have h2 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 y := hasDerivAt_const y 1
    have h3 := h2.sub h1
    refine h3.congr_deriv ?_
    ring
  have h_sqrt : HasDerivAt (fun z => Real.sqrt (1 - z ^ 2)) ((-2 * y) / (2 * Real.sqrt (1 - y ^ 2))) y :=
    h_inner.sqrt hne
  have h_pow : HasDerivAt (fun z => (Real.sqrt (1 - z ^ 2)) ^ 3)
      (3 * (Real.sqrt (1 - y ^ 2)) ^ 2 * (((-2 * y) / (2 * Real.sqrt (1 - y ^ 2))))) y :=
    h_sqrt.pow 3
  have hJ : HasDerivAt Jfun
      ((S2fun y - H2fun y) * (Real.sqrt (1 - y ^ 2)) ^ 3
        + (Dfun y - H1fun y) * (3 * (Real.sqrt (1 - y ^ 2)) ^ 2 * (((-2 * y) / (2 * Real.sqrt (1 - y ^ 2)))))) y :=
    hK.mul h_pow
  refine hJ.congr_deriv ?_
  have hK0 := hodeK y hy
  field_simp
  linear_combination (Real.sqrt (1 - y ^ 2)) * hK0
    + (S2fun y - H2fun y) * (Real.sqrt (1 - y ^ 2)) * hsq

theorem K_eq_zero (y : ℝ) (hy : |y| < 1) : Dfun y - H1fun y = 0 := by
  set s := Metric.ball (0 : ℝ) 1 with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hs_conn : IsPreconnected s := (convex_ball (0 : ℝ) 1).isPreconnected
  have hmem : ∀ z ∈ s, |z| < 1 := fun z hz => (mem_ball_zero_iff z 1).mp hz
  have hdiff : DifferentiableOn ℝ Jfun s := by
    intro z hz
    exact ((hasDerivAt_Jfun z (hmem z hz)).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn (deriv Jfun) 0 s := by
    intro z hz
    have h := (hasDerivAt_Jfun z (hmem z hz)).deriv
    simp [h]
  have hJ0 : Jfun 0 = 0 := by simp [Jfun, Dfun_zero, H1fun_zero]
  have h0mem : (0:ℝ) ∈ s := (mem_ball_zero_iff 0 1).mpr (by norm_num)
  have hymem : y ∈ s := (mem_ball_zero_iff y 1).mpr hy
  have hJy : Jfun y = Jfun 0 := hs_open.is_const_of_deriv_eq_zero hs_conn hdiff hderiv hymem h0mem
  rw [hJ0] at hJy
  have hpos : (0:ℝ) < 1 - y ^ 2 := hpos_of_mem y hy
  have hne3 : (Real.sqrt (1 - y ^ 2)) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (Real.sqrt_ne_zero'.mpr hpos)
  simp only [Jfun] at hJy
  exact (mul_eq_zero.mp hJy).resolve_right hne3

theorem SH_eq (y : ℝ) (hy : |y| < 1) : Sfun y = Hfun y := by
  set s := Metric.ball (0 : ℝ) 1 with hs_def
  have hs_open : IsOpen s := Metric.isOpen_ball
  have hs_conn : IsPreconnected s := (convex_ball (0 : ℝ) 1).isPreconnected
  have hmem : ∀ z ∈ s, |z| < 1 := fun z hz => (mem_ball_zero_iff z 1).mp hz
  have hL : ∀ z ∈ s, HasDerivAt (fun w => Sfun w - Hfun w) 0 z := by
    intro z hz
    have hz1 := hmem z hz
    have h := (hasDerivAt_Sfun z hz1).sub (hasDerivAt_H z hz1)
    have hK := K_eq_zero z hz1
    refine h.congr_deriv ?_
    linarith [hK]
  have hdiff : DifferentiableOn ℝ (fun w => Sfun w - Hfun w) s := by
    intro z hz
    exact ((hL z hz).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn (deriv (fun w => Sfun w - Hfun w)) 0 s := by
    intro z hz
    have h := (hL z hz).deriv
    simp [h]
  have h0mem : (0:ℝ) ∈ s := (mem_ball_zero_iff 0 1).mpr (by norm_num)
  have hymem : y ∈ s := (mem_ball_zero_iff y 1).mpr hy
  have hLy : (Sfun y - Hfun y) = (Sfun 0 - Hfun 0) :=
    hs_open.is_const_of_deriv_eq_zero hs_conn hdiff hderiv hymem h0mem
  rw [Sfun_zero, Hfun_zero] at hLy
  linarith [hLy]

/--
Arcsin power series via central binomial reciprocals.

Source: B. Sury, Tianming Wang, and Feng-Zhen Zhao, "Identities
Involving Reciprocals of Binomial Coefficients," Journal of Integer
Sequences 7 (2004), Article 04.2.8, Theorem, lines 365–371,
https://cs.uwaterloo.ca/journals/JIS/VOL7/Sury/sury99.tex

The source attributes the identity to D. H. Lehmer. The sum over
`m ≥ 1` is indexed by `m + 1` over `ℕ`.
Proves `Wanted` entry `arcsin_central_binomial_reciprocal_series`.
-/
theorem arcsin_central_binomial_reciprocal_series
    (x : ℝ)
    (hx : |x| < 1) :
    HasSum (fun m : ℕ =>
        (2 * x) ^ (2 * (m + 1)) / ((↑(m + 1) : ℝ) * ↑(Nat.choose (2 * (m + 1)) (m + 1))))
      ((2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x) := by
  have hSH : Sfun x = Hfun x := SH_eq x hx
  have hsum := (summable_Aterm x hx).hasSum
  have hsumH : HasSum (Aterm x) (Hfun x) := hSH ▸ hsum
  have hbase : HasSum (Aterm x) (Hfun x + ∑ i ∈ Finset.range 1, Aterm x i) := by
    rw [Finset.sum_range_one, Aterm_zero, add_zero]
    exact hsumH
  have hshifted : HasSum (fun m => Aterm x (m + 1)) (Hfun x) :=
    (hasSum_nat_add_iff 1).mpr hbase
  show HasSum (fun m => Aterm x (m + 1)) (Hfun x)
  exact hshifted

end MetaMathlibExt
