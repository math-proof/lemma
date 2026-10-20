/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean -/

import sympy.atlas.Analysis.LaplaceTransform.Basic
/-!
# Elementary Laplace-transform API

Algebra and convergence rules, right-half-plane monotonicity, the exponential
parameter shift, and the scalar constant-one transform, following the conventions
of Mathlib's `MellinTransform.lean`.

## Source correspondence

The source is Andrew V. Sutherland, *18.785 Number Theory I*, Lecture 16,
[Definition 16.9 and the following properties](https://math.mit.edu/classes/18.785/2021fa/LectureNotes16.pdf#page=6).
It defines
`ℒh(s) = ∫₀^∞ exp(-st) h(t) dt` on the positive real ray and records linearity,
the transform of a constant, and the exponential parameter shift.

The Stage 1 definitions used here integrate over `Set.Ioi 0`, exactly the source domain
`ℝ_{>0}`.  `LaplaceConvergent f s` is integrability of
`t ↦ exp(-st) • f(t)` on that ray, and `HasLaplace f s v` combines this convergence
with `laplace f s = v`.  Thus the declarations below map as follows.

* `hasLaplace_add`, `hasLaplace_sub`, and `hasLaplace_const_smul` are the source's
  linearity laws.  They generalize real-valued functions and real scalars to functions in a
  complex normed space and complex scalars.
* `LaplaceConvergent.mono_re` makes explicit the standard convergence fact that convergence
  at `s` persists when the real part of the parameter increases.
* `LaplaceConvergent.exp_smul`, `laplace_exp_smul`, and
  `hasLaplace_exp_smul_iff` formalize `ℒ(exp(at)h(t))(s) = ℒh(s-a)`.
* `hasLaplace_one` is the source's constant-function formula at `a = 1`, with the exact
  convergence hypothesis `0 < s.re`; complex scalar multiplication then gives the general
  constant formula.

Piecewise continuity and exponential growth in Definition 16.9 are sufficient hypotheses for
convergence and holomorphy.  This Stage 2 API assumes the exact integrability condition at the
requested parameter; the holomorphy consequence is deliberately outside this module.
-/

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem LaplaceConvergent.const_smul {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) (c : ℂ) :
    LaplaceConvergent (fun t => c • f t) s := by
  unfold LaplaceConvergent at hf ⊢
  refine (hf.smul c).congr ?_
  filter_upwards with t
  exact smul_comm c (Complex.exp (-s * (t : ℂ))) (f t)

theorem hasLaplace_zero (s : ℂ) :
    HasLaplace (fun _ : ℝ => (0 : E)) s 0 := by
  refine ⟨?_, ?_⟩
  · unfold LaplaceConvergent
    have hfun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (0 : E)) =
        (fun _ : ℝ => (0 : E)) :=
      funext fun t => smul_zero _
    rw [hfun]
    exact integrableOn_zero
  · unfold laplace
    have hfun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (0 : E)) =
        (fun _ : ℝ => (0 : E)) :=
      funext fun t => smul_zero _
    rw [hfun]
    exact MeasureTheory.integral_zero ℝ E

theorem hasLaplace_add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    HasLaplace (f + g) s (laplace f s + laplace g s) := by
  refine ⟨?_, ?_⟩
  · simpa only [LaplaceConvergent, Pi.add_apply, smul_add] using! hf.add hg
  · unfold laplace
    simp only [Pi.add_apply, smul_add]
    exact integral_add hf hg

theorem hasLaplace_sub {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    HasLaplace (f - g) s (laplace f s - laplace g s) := by
  refine ⟨?_, ?_⟩
  · simpa only [LaplaceConvergent, Pi.sub_apply, smul_sub] using! hf.sub hg
  · unfold laplace
    simp only [Pi.sub_apply, smul_sub]
    exact integral_sub hf hg

theorem hasLaplace_const_smul {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) (c : ℂ) :
    HasLaplace (fun t => c • f t) s (c • laplace f s) := by
  refine ⟨hf.const_smul c, ?_⟩
  unfold laplace
  simp only [smul_comm _ c]
  exact Integrable.integral_smul c hf

theorem LaplaceConvergent.mono_re {f : ℝ → E} {s w : ℂ}
    (hf : LaplaceConvergent f s) (hsw : s.re ≤ w.re) :
    LaplaceConvergent f w := by
  unfold LaplaceConvergent at hf ⊢
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(w - s) * (t : ℂ)))
      (volume.restrict (Set.Ioi 0)) := by
    fun_prop
  have hbound : ∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))),
      ‖Complex.exp (-(w - s) * (t : ℂ))‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with (t : ℝ) ht
    rw [Set.mem_Ioi] at ht
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hre : (-(w - s) * (t : ℂ)).re = (s.re - w.re) * t := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ht)
  have hbase : Integrable
      (fun t : ℝ => Complex.exp (-(w - s) * (t : ℂ)) •
        (Complex.exp (-s * (t : ℂ)) • f t))
      (volume.restrict (Set.Ioi 0)) :=
    Integrable.bdd_smul hf 1 hmeas hbound
  refine hbase.congr (Filter.Eventually.of_forall fun (t : ℝ) => ?_)
  change Complex.exp (-(w - s) * (t : ℂ)) •
      (Complex.exp (-s * (t : ℂ)) • f t) =
    Complex.exp (-w * (t : ℂ)) • f t
  have hexp : (-(w - s) * (t : ℂ)) + (-s * (t : ℂ)) = -w * (t : ℂ) := by
    ring
  rw [smul_smul, ← Complex.exp_add, hexp]

theorem LaplaceConvergent.exp_smul {f : ℝ → E} (s a : ℂ) :
    LaplaceConvergent (fun t => Complex.exp (a * (t : ℂ)) • f t) s ↔
      LaplaceConvergent f (s - a) := by
  unfold LaplaceConvergent
  refine integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi
  change Complex.exp (-s * (t : ℂ)) • (Complex.exp (a * (t : ℂ)) • f t) =
    Complex.exp (-(s - a) * (t : ℂ)) • f t
  have hexp : (-s * (t : ℂ)) + (a * (t : ℂ)) = -(s - a) * (t : ℂ) := by
    ring
  rw [smul_smul, ← Complex.exp_add, hexp]

theorem laplace_exp_smul (f : ℝ → E) (s a : ℂ) :
    laplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s =
      laplace f (s - a) := by
  unfold laplace
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  change Complex.exp (-s * (t : ℂ)) • (Complex.exp (a * (t : ℂ)) • f t) =
    Complex.exp (-(s - a) * (t : ℂ)) • f t
  have hexp : (-s * (t : ℂ)) + (a * (t : ℂ)) = -(s - a) * (t : ℂ) := by
    ring
  rw [smul_smul, ← Complex.exp_add, hexp]

theorem hasLaplace_exp_smul_iff {f : ℝ → E} (s a : ℂ) (v : E) :
    HasLaplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s v ↔
      HasLaplace f (s - a) v := by
  unfold HasLaplace
  rw [LaplaceConvergent.exp_smul, laplace_exp_smul]

theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ => (1 : ℂ)) s s⁻¹ := by
  refine ⟨?_, ?_⟩
  · unfold LaplaceConvergent
    simp only [smul_eq_mul, mul_one]
    exact integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  · unfold laplace
    simp only [smul_eq_mul, mul_one]
    rw [integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0]
    simp [div_eq_mul_inv]
