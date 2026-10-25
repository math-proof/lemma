import Mathlib
import sympy.Basic
import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM17.Schrodinger
open MeasureTheory Complex FourierTransform SchrodingerEquation


namespace SchrodingerEquation

/--
[schrodingerKernel_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma schrodingerKernel_norm
  {n : ℕ}
  {t : ℝ}
  {x : Rn n}
-- given
  (ht : t > 0) :
-- imply
  ‖schrodingerKernel t x‖ = (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) := by
-- proof
  unfold schrodingerKernel
  rw [norm_mul]
  have hexp : ‖exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, mul_one]
  have hcast : (-(↑n : ℂ) / 2) = (↑(-(↑n : ℝ) / 2) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_real]
  have hnorm : ‖((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)‖ = 2 * Real.pi * t := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_real, Complex.norm_I, mul_one]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    rw [Real.norm_of_nonneg (le_of_lt ht)]
  rw [hnorm]

end SchrodingerEquation

namespace SchrodingerEquation

/--
[schrodingerKernel1D_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma schrodingerKernel1D_norm
  {t : ℝ}
  {x : ℝ}
-- given
  (ht : t > 0) :
-- imply
  ‖schrodingerKernel1D t x‖ = 1 / Real.sqrt (2 * Real.pi * t) := by
-- proof
  unfold schrodingerKernel1D
  rw [norm_mul]
  have hexp : ‖exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  rw [hexp, mul_one]
  have hcast : (-(1 : ℂ) / 2) = (↑((-1 : ℝ) / 2) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_real]
  have hnorm : ‖((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)‖ = 2 * Real.pi * t := by
    rw [norm_mul, norm_mul]
    simp only [Complex.norm_real, Complex.norm_I, mul_one]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    rw [Real.norm_of_nonneg (le_of_lt ht)]
  rw [hnorm]
  have hpos : 0 < 2 * Real.pi * t := by positivity
  rw [show (-1 : ℝ) / 2 = -(1/2 : ℝ) from by ring]
  rw [Real.rpow_neg (le_of_lt hpos)]
  rw [← Real.sqrt_eq_rpow]
  rw [one_div]

end SchrodingerEquation

namespace SchrodingerEquation

/--
[schrodingerKernel1D_time_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma schrodingerKernel1D_time_deriv
  {t x : ℝ}
-- given
  (ht : t > 0) :
-- imply
  I * deriv (fun s => schrodingerKernel1D s x) t = schrodingerKernel1D t x * (-I / (2 * ↑t) + (↑(x ^ 2) : ℂ) / (2 * ↑t ^ 2)) := by
-- proof
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have htne_c : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_ne
  set c2pi := (↑(2 * Real.pi) : ℂ) with hc2pi_def
  have hc2pi_ne : c2pi ≠ 0 := by simp only [c2pi, ofReal_ne_zero]; positivity
  have hbase_ne : c2pi * I * ↑t ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc2pi_ne I_ne_zero) htne_c
  have hbase_mem : c2pi * I * ↑t ∈ Complex.slitPlane := by
    have heq : c2pi * I * ↑t = ↑(2 * Real.pi * t) * I := by simp [c2pi]; ring
    rw [heq, Complex.mem_slitPlane_iff]; right
    simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]; positivity
  have hderiv_cpow : HasDerivAt (fun s : ℝ => (c2pi * I * ↑s) ^ ((-1 : ℂ) / 2))
    ((-1 : ℂ) / 2 * (c2pi * I * ↑t) ^ ((-1 : ℂ) / 2 - 1) * (c2pi * I)) t := by
    have hlin : HasDerivAt (fun z : ℂ => c2pi * I * z) (c2pi * I) (↑t : ℂ) := by
      have h2 := (hasDerivAt_id (↑t : ℂ)).const_mul (c2pi * I)
      simp [mul_one] at h2; exact h2
    exact (hlin.cpow_const hbase_mem).comp_ofReal
  have hderiv_exp : HasDerivAt (fun s : ℝ => exp (I * ((x ^ 2 / (2 * s) : ℝ) : ℂ)))
    (exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ)) * (I * ((-x ^ 2 / (2 * t ^ 2) : ℝ) : ℂ))) t := by
    have hq : HasDerivAt (fun s : ℝ => (x ^ 2 / (2 * s) : ℝ)) (-x ^ 2 / (2 * t ^ 2)) t := by
      have := (hasDerivAt_inv ht_ne).const_mul (x ^ 2 / 2)
      simp only [mul_neg] at this
      convert this using 1 <;> [ext s; skip] <;> ring
    exact (hq.ofReal_comp.const_mul I).cexp
  have hK : HasDerivAt (fun s => schrodingerKernel1D s x)
    (((-1 : ℂ) / 2 * (c2pi * I * ↑t) ^ ((-1 : ℂ) / 2 - 1) * (c2pi * I)) *
      exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ)) +
    (c2pi * I * ↑t) ^ ((-1 : ℂ) / 2) *
      (exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ)) * (I * ((-x ^ 2 / (2 * t ^ 2) : ℝ) : ℂ)))) t := by
    have hprod := hderiv_cpow.mul hderiv_exp
    have : (fun s => (c2pi * I * ↑s) ^ ((-1 : ℂ) / 2) *
      exp (I * ((x ^ 2 / (2 * s) : ℝ) : ℂ))) = (fun s => schrodingerKernel1D s x) := by
      funext s; simp only [schrodingerKernel1D]; ring
    rwa [← this]
  rw [hK.deriv]
  set z := c2pi * I * (↑t : ℂ)
  set e := exp (I * ((x ^ 2 / (2 * t) : ℝ) : ℂ))
  have hcpow_sub : z ^ ((-1 : ℂ) / 2 - 1) = z ^ ((-1 : ℂ) / 2) / z := by
    have h := Complex.cpow_sub ((-1 : ℂ) / 2) 1 hbase_ne
    rw [cpow_one] at h; exact h
  rw [hcpow_sub]
  have hz_div : c2pi * I / z = 1 / ↑t := by simp only [z]; field_simp
  rw [show (-1 : ℂ) / 2 * (z ^ ((-1 : ℂ) / 2) / z) * (c2pi * I) =
    z ^ ((-1 : ℂ) / 2) * ((-1 : ℂ) / 2 * (c2pi * I / z)) from by ring]
  rw [hz_div]
  have hKval : schrodingerKernel1D t x = z ^ ((-1 : ℂ) / 2) * e := by
    simp only [schrodingerKernel1D, z, e]; ring
  rw [hKval]
  ring_nf
  rw [I_sq]
  push_cast
  ring_nf

end SchrodingerEquation

namespace SchrodingerEquation

/--
[schrodingerKernel1D_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma schrodingerKernel1D_laplacian
  {t x : ℝ}
-- given
  (ht : t > 0) :
-- imply
  (1 / 2 : ℂ) * deriv (deriv (schrodingerKernel1D t)) x = schrodingerKernel1D t x * (I / (2 * ↑t) - (↑(x ^ 2) : ℂ) / (2 * ↑t ^ 2)) := by
-- proof
  have hK_deriv : ∀ y : ℝ, HasDerivAt (schrodingerKernel1D t)
    (schrodingerKernel1D t y * (I * ↑y / ↑t)) y := by
    intro y
    unfold schrodingerKernel1D
    set C := (((2 * Real.pi : ℝ) : ℂ) * I * (t : ℂ)) ^ (-(1 : ℂ) / 2)
    have hg : HasDerivAt (fun z : ℝ => (z ^ 2 / (2 * t) : ℝ)) (y / t) y := by
      have h : HasDerivAt (fun z : ℝ => z ^ 2) (2 * y) y := by
        have := hasDerivAt_pow 2 y; simp at this; exact this
      convert h.div_const (2 * t) using 1; field_simp
    have hIg : HasDerivAt (fun z : ℝ => I * ((z ^ 2 / (2 * t) : ℝ) : ℂ)) (I * ↑(y / t)) y :=
      (HasDerivAt.ofReal_comp hg).const_mul I
    have hexp := HasDerivAt.cexp hIg
    have hfull := hexp.const_mul C
    convert hfull using 1
    push_cast; ring
  have h_deriv_eq : deriv (schrodingerKernel1D t) =
    fun y => schrodingerKernel1D t y * (I * ↑y / ↑t) := by
    ext y; exact (hK_deriv y).deriv
  rw [h_deriv_eq]
  have hg : HasDerivAt (fun y : ℝ => I * (↑y : ℂ) / (↑t : ℂ)) (I / ↑t) x := by
    have h : HasDerivAt (⇑ofRealCLM) (ofRealCLM 1) x := ContinuousLinearMap.hasDerivAt ofRealCLM
    simp [ofRealCLM_apply, ofReal_one] at h
    have h2 := (h.const_mul I).div_const (↑t : ℂ)
    convert h2 using 1; ring
  have h_prod : HasDerivAt (fun y => schrodingerKernel1D t y * (I * ↑y / ↑t))
    (schrodingerKernel1D t x * (I * ↑x / ↑t) * (I * ↑x / ↑t) +
      schrodingerKernel1D t x * (I / ↑t)) x :=
    (hK_deriv x).mul hg
  rw [h_prod.deriv]
  have ht' : (↑t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have key : schrodingerKernel1D t x * (I * ↑x / ↑t) * (I * ↑x / ↑t) =
    schrodingerKernel1D t x * (I ^ 2 * (↑x) ^ 2 / (↑t) ^ 2) := by ring
  rw [key, I_sq]
  push_cast
  field_simp
  ring

end SchrodingerEquation

namespace SchrodingerEquation

/--
[lemma_2_0_2_K_solves_schrodinger](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma lemma_2_0_2_K_solves_schrodinger
-- imply
  IsFreeSchrodingerSolution (fun t x => schrodingerKernel1D t x) := by
-- proof
  intro t ht x
  rw [schrodingerKernel1D_time_deriv t x ht, schrodingerKernel1D_laplacian t x ht]
  ring

end SchrodingerEquation

namespace SchrodingerEquation

/--
[schrodingerKernel_time_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma schrodingerKernel_time_deriv
  {n : ℕ}
  {t : ℝ}
  {x : Rn n}
-- given
  (ht : t > 0) :
-- imply
  I * deriv (fun s => schrodingerKernel (n := n) s x) t = schrodingerKernel t x * (-(↑n : ℂ) * I / (2 * ↑t) + (↑(‖x‖ ^ 2) : ℂ) / (2 * ↑t ^ 2)) := by
-- proof
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have htne_c : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_ne
  set c2pi := (↑(2 * Real.pi) : ℂ) with hc2pi_def
  have hc2pi_ne : c2pi ≠ 0 := by simp only [c2pi, ofReal_ne_zero]; positivity
  have hbase_ne : c2pi * I * ↑t ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc2pi_ne I_ne_zero) htne_c
  have hbase_mem : c2pi * I * ↑t ∈ Complex.slitPlane := by
    have heq : c2pi * I * ↑t = ↑(2 * Real.pi * t) * I := by simp [c2pi]; ring
    rw [heq, Complex.mem_slitPlane_iff]; right
    simp [mul_im, ofReal_re, ofReal_im, I_re, I_im]; positivity
  have hderiv_cpow : HasDerivAt (fun s : ℝ => (c2pi * I * ↑s) ^ (-(↑n : ℂ) / 2))
    (-(↑n : ℂ) / 2 * (c2pi * I * ↑t) ^ (-(↑n : ℂ) / 2 - 1) * (c2pi * I)) t := by
    have hlin : HasDerivAt (fun z : ℂ => c2pi * I * z) (c2pi * I) (↑t : ℂ) := by
      have h2 := (hasDerivAt_id (↑t : ℂ)).const_mul (c2pi * I)
      simp [mul_one] at h2; exact h2
    exact (hlin.cpow_const hbase_mem).comp_ofReal
  have hderiv_exp : HasDerivAt (fun s : ℝ => exp (I * ((‖x‖ ^ 2 / (2 * s) : ℝ) : ℂ)))
    (exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ)) *
      (I * ((-‖x‖ ^ 2 / (2 * t ^ 2) : ℝ) : ℂ))) t := by
    have hq : HasDerivAt (fun s : ℝ => (‖x‖ ^ 2 / (2 * s) : ℝ))
      (-‖x‖ ^ 2 / (2 * t ^ 2)) t := by
      have := (hasDerivAt_inv ht_ne).const_mul (‖x‖ ^ 2 / 2)
      simp only [mul_neg] at this
      convert this using 1 <;> [ext s; skip] <;> ring
    exact (hq.ofReal_comp.const_mul I).cexp
  have hK : HasDerivAt (fun s => schrodingerKernel (n := n) s x)
    ((-(↑n : ℂ) / 2 * (c2pi * I * ↑t) ^ (-(↑n : ℂ) / 2 - 1) * (c2pi * I)) *
      exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ)) +
    (c2pi * I * ↑t) ^ (-(↑n : ℂ) / 2) *
      (exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ)) *
        (I * ((-‖x‖ ^ 2 / (2 * t ^ 2) : ℝ) : ℂ)))) t := by
    have hprod := hderiv_cpow.mul hderiv_exp
    have : (fun s => (c2pi * I * ↑s) ^ (-(↑n : ℂ) / 2) *
      exp (I * ((‖x‖ ^ 2 / (2 * s) : ℝ) : ℂ))) =
      (fun s => schrodingerKernel (n := n) s x) := by
      funext s; simp only [schrodingerKernel]; ring
    rwa [← this]
  rw [hK.deriv]
  set z := c2pi * I * (↑t : ℂ)
  set e := exp (I * ((‖x‖ ^ 2 / (2 * t) : ℝ) : ℂ))
  have hcpow_sub : z ^ (-(↑n : ℂ) / 2 - 1) = z ^ (-(↑n : ℂ) / 2) / z := by
    have h := Complex.cpow_sub (-(↑n : ℂ) / 2) 1 hbase_ne
    rw [cpow_one] at h; exact h
  rw [hcpow_sub]
  have hz_div : c2pi * I / z = 1 / ↑t := by simp only [z]; field_simp
  rw [show -(↑n : ℂ) / 2 * (z ^ (-(↑n : ℂ) / 2) / z) * (c2pi * I) =
    z ^ (-(↑n : ℂ) / 2) * (-(↑n : ℂ) / 2 * (c2pi * I / z)) from by ring]
  rw [hz_div]
  have hKval : schrodingerKernel t x = z ^ (-(↑n : ℂ) / 2) * e := by
    simp only [schrodingerKernel, z, e]; ring
  rw [hKval]
  ring_nf
  rw [I_sq]
  push_cast
  ring_nf

end SchrodingerEquation

namespace SchrodingerEquation

/--
[theorem_2_1_dispersive_estimate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma theorem_2_1_dispersive_estimate
  {φ : ℝ → ℂ}
  {t : ℝ}
  {x : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  ‖schrodingerSolution φ t x‖ ≤ (1 / Real.sqrt (2 * Real.pi * t)) * ∫ y : ℝ, ‖φ y‖ := by
-- proof
  show ‖∫ y : ℝ, schrodingerKernel1D t (x - y) * φ y‖ ≤ _
  calc ‖∫ y : ℝ, schrodingerKernel1D t (x - y) * φ y‖
    ≤ ∫ y : ℝ, ‖schrodingerKernel1D t (x - y) * φ y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, ‖schrodingerKernel1D t (x - y)‖ * ‖φ y‖ := by
      congr 1; ext y; exact norm_mul _ _
    _ = ∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * t)) * ‖φ y‖ := by
      congr 1; ext y
      rw [schrodingerKernel1D_norm t (x - y) ht]
    _ = (1 / Real.sqrt (2 * Real.pi * t)) * ∫ y : ℝ, ‖φ y‖ :=
      integral_const_mul _ _

end SchrodingerEquation

namespace SchrodingerEquation

/--
[theorem_2_1_dispersive_estimate_nD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma theorem_2_1_dispersive_estimate_nD
  {n : ℕ}
  {φ : Rn n → ℂ}
  {t : ℝ}
  {x : Rn n}
-- given
  (ht : 0 < t) :
-- imply
  ‖schrodingerSolutionND φ t x‖ ≤ (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) * ∫ y : Rn n, ‖φ y‖ := by
-- proof
  show ‖∫ y : Rn n, schrodingerKernel t (x - y) * φ y‖ ≤ _
  calc ‖∫ y : Rn n, schrodingerKernel t (x - y) * φ y‖
    ≤ ∫ y : Rn n, ‖schrodingerKernel t (x - y) * φ y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : Rn n, ‖schrodingerKernel t (x - y)‖ * ‖φ y‖ := by
      congr 1; ext y; exact norm_mul _ _
    _ = ∫ y : Rn n, (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) * ‖φ y‖ := by
      congr 1; ext y
      rw [schrodingerKernel_norm t (x - y) ht]
    _ = (2 * Real.pi * t) ^ (-(↑n : ℝ) / 2) * ∫ y : Rn n, ‖φ y‖ :=
      integral_const_mul _ _

end SchrodingerEquation

namespace SchrodingerEquation

/--
[fourier_solution_norm_sq_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma fourier_solution_norm_sq_eq
  {φ : ℝ → ℂ}
  {t ξ : ℝ} :
-- imply
  ‖solutionFT φ t ξ‖ = ‖CM16.fourierTransform φ ξ‖ := by
-- proof
  unfold solutionFT
  rw [norm_mul]
  simp only [fundamentalSolutionFT, norm_exp_ofReal_mul_I, one_mul]

end SchrodingerEquation

namespace SchrodingerEquation

/--
[fourierTransform_eq_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma fourierTransform_eq_fourier
  {f : ℝ → ℂ}
  {ξ : ℝ} :
-- imply
  CM16.fourierTransform f ξ = 𝓕 f ξ :=
-- proof
  CM16.fourierTransform_eq_mathlib_fourier f ξ
set_option maxHeartbeats 400000 in

end SchrodingerEquation

namespace SchrodingerEquation

/--
[plancherel_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma plancherel_theorem
  {f : ℝ → ℂ}
-- given
  (hf_smooth : ContDiff ℝ ⊤ f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ∫ x, ‖f x‖ ^ 2 = ∫ ξ, ‖CM16.fourierTransform f ξ‖ ^ 2 := by
-- proof
  have hf_smooth' : ContDiff ℝ (↑(⊤ : ℕ∞)) f := hf_smooth.of_le le_top
  let sf : SchwartzMap ℝ ℂ := hf_supp.toSchwartzMap hf_smooth'
  have h_eq_f : ∀ x, sf x = f x := HasCompactSupport.toSchwartzMap_toFun hf_supp hf_smooth'
  have h := SchwartzMap.integral_norm_sq_fourier sf
  have hlhs : ∫ ξ : ℝ, ‖(𝓕 sf) ξ‖ ^ 2 = ∫ ξ, ‖CM16.fourierTransform f ξ‖ ^ 2 := by
    congr 1; ext ξ
    show ‖𝓕 (⇑sf) ξ‖ ^ 2 = ‖CM16.fourierTransform f ξ‖ ^ 2
    rw [show (⇑sf : ℝ → ℂ) = f from funext h_eq_f,
      show 𝓕 f ξ = CM16.fourierTransform f ξ from (fourierTransform_eq_fourier f ξ).symm]
  have hrhs : ∫ x : ℝ, ‖sf x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    apply integral_congr_ae; filter_upwards with x; rw [h_eq_f x]
  linarith

end SchrodingerEquation

namespace SchrodingerEquation

/--
[fourier_solution_norm_sq_eq_nD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma fourier_solution_norm_sq_eq_nD
  {n : ℕ}
  {φ : Rn n → ℂ}
  {t : ℝ}
  {ξ : Rn n} :
-- imply
  ‖solutionFT_nD φ t ξ‖ = ‖fourierTransformRn φ ξ‖ := by
-- proof
  unfold solutionFT_nD
  rw [norm_mul]
  simp only [fundamentalSolutionFT_nD, norm_exp_ofReal_mul_I, one_mul]

end SchrodingerEquation

namespace SchrodingerEquation

/--
[fourierTransformRn_eq_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma fourierTransformRn_eq_fourier
  {n : ℕ}
  {f : Rn n → ℂ}
  {ξ : Rn n} :
-- imply
  fourierTransformRn f ξ = 𝓕 f ξ := by
-- proof
  unfold fourierTransformRn; rw [Real.fourier_eq']
  congr 1; ext x
  simp only [smul_eq_mul, mul_comm (cexp _) (f x)]
  congr 1; rw [real_inner_comm ξ x]
set_option maxHeartbeats 400000 in

end SchrodingerEquation

namespace SchrodingerEquation

/--
[plancherel_compact_support_nD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma plancherel_compact_support_nD
  {n : ℕ}
  {f : Rn n → ℂ}
-- given
  (hf_smooth : ContDiff ℝ ⊤ f)
  (hf_supp : HasCompactSupport f) :
-- imply
  ∫ x : Rn n, ‖f x‖ ^ 2 = ∫ ξ : Rn n, ‖fourierTransformRn f ξ‖ ^ 2 := by
-- proof
  have hf_smooth' : ContDiff ℝ (↑(⊤ : ℕ∞)) f := hf_smooth.of_le le_top
  let sf : SchwartzMap (Rn n) ℂ := hf_supp.toSchwartzMap hf_smooth'
  have h_eq_f : ∀ x, sf x = f x := HasCompactSupport.toSchwartzMap_toFun hf_supp hf_smooth'
  have h := SchwartzMap.integral_norm_sq_fourier sf
  have hlhs : ∫ ξ : Rn n, ‖(𝓕 sf) ξ‖ ^ 2 = ∫ ξ, ‖fourierTransformRn f ξ‖ ^ 2 := by
    congr 1; ext ξ
    show ‖𝓕 (⇑sf) ξ‖ ^ 2 = ‖fourierTransformRn f ξ‖ ^ 2
    rw [show (⇑sf : Rn n → ℂ) = f from funext h_eq_f,
      show 𝓕 f ξ = fourierTransformRn f ξ from (fourierTransformRn_eq_fourier f ξ).symm]
  have hrhs : ∫ x : Rn n, ‖sf x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    apply integral_congr_ae; filter_upwards with x; rw [h_eq_f x]
  linarith

end SchrodingerEquation

namespace SchrodingerEquation

/--
[FT_kernel_translation_nD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma FT_kernel_translation_nD
  {n : ℕ}
  {t : ℝ}
  {ξ y : Rn n}
-- given
  (ht : 0 < t) :
-- imply
  ∫ (x : Rn n), schrodingerKernel t (x - y) * cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) = cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ y) * I) * fourierTransformRn (schrodingerKernel t) ξ := by
-- proof
  have subst : ∫ (x : Rn n), schrodingerKernel t (x - y) *
    cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I) =
    ∫ (u : Rn n), schrodingerKernel t u *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I) := by
    rw [show (fun x => schrodingerKernel t (x - y) *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ x) * I)) =
      (fun x => (fun u => schrodingerKernel t u *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I)) (x - y)) from by
      ext x; congr 1; congr 1; congr 1; congr 1; congr 1; rw [sub_add_cancel]]
    exact integral_sub_right_eq_self
      (fun u => schrodingerKernel t u *
        cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I)) y
  rw [subst]
  have inner_split : ∀ u : Rn n,
    schrodingerKernel t u *
      cexp (↑(-2 * Real.pi * @inner ℝ (Rn n) _ ξ (u + y)) * I) =
    cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I) *
    (schrodingerKernel t u *
      cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I)) := by
    intro u
    rw [inner_add_right]
    have : ((-2 * Real.pi * (@inner ℝ (Rn n) _ ξ u + @inner ℝ (Rn n) _ ξ y) : ℝ) : ℂ) * I =
      ((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I +
      ((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, exp_add]; ring
  simp_rw [inner_split]
  simp_rw [show ∀ u : Rn n,
    cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I) *
    (schrodingerKernel t u *
      cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I)) =
    cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ y : ℝ) : ℂ) * I) •
    (schrodingerKernel t u *
      cexp (((-2 * Real.pi * @inner ℝ (Rn n) _ ξ u : ℝ) : ℂ) * I)) from by
    intro u; rw [smul_eq_mul]]
  rw [integral_smul, smul_eq_mul]
  rfl

end SchrodingerEquation

namespace SchrodingerEquation

/--
[norm_sq_eq_sum_sq_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM17/Schrodinger.lean)
-/
@[path]
lemma norm_sq_eq_sum_sq_real
  {n : ℕ}
  {ξ : Rn n} :
-- imply
  ∑ i : Fin n, (ξ i) ^ 2 = ‖ξ‖ ^ 2 := by
-- proof
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  congr 1; simp [Real.norm_eq_abs, sq_abs]
/-- The Fourier transform of the 1D complex Gaussian
$\frac{1}{(2\pi i t)^{1/2}} e^{i u^2 / (2t)}$ at frequency $\xi$ equals
$e^{-2\pi^2 i t \xi^2}$. -/

end SchrodingerEquation


-- created on 2026-10-23
