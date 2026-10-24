import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.LaplaceTransform.Basic
open MeasureTheory


/--
[LaplaceConvergent.const_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma LaplaceConvergent.const_smul
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s c : ℂ}
-- given
  (hf : LaplaceConvergent f s) :
-- imply
  LaplaceConvergent (fun t => c • f t) s := by
-- proof
  unfold LaplaceConvergent at hf ⊢
  refine (hf.smul c).congr ?_
  filter_upwards with t
  exact smul_comm c (Complex.exp (-s * (t : ℂ))) (f t)

/--
[hasLaplace_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma hasLaplace_zero
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {s : ℂ} :
-- imply
  HasLaplace (fun _ : ℝ => (0 : E)) s 0 := by
-- proof
  refine ⟨?_, ?_⟩
  · unfold LaplaceConvergent
    have hfun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (0 : E)) =
      (fun _ : ℝ => (0 : E)) :=
      funext fun t => smul_zero _
    rwa [hfun]
  · unfold laplace
    have hfun : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • (0 : E)) =
      (fun _ : ℝ => (0 : E)) :=
      funext fun t => smul_zero _
    rw [hfun]
    exact MeasureTheory.integral_zero ℝ E

/--
[hasLaplace_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma hasLaplace_add
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℝ → E}
  {s : ℂ}
-- given
  (hf : LaplaceConvergent f s)
  (hg : LaplaceConvergent g s) :
-- imply
  HasLaplace (f + g) s (laplace f s + laplace g s) := by
-- proof
  refine ⟨?_, ?_⟩
  · simpa only [LaplaceConvergent, Pi.add_apply, smul_add] using! hf.add hg
  · unfold laplace
    simp only [Pi.add_apply, smul_add]
    exact integral_add hf hg

/--
[hasLaplace_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma hasLaplace_sub
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℝ → E}
  {s : ℂ}
-- given
  (hf : LaplaceConvergent f s)
  (hg : LaplaceConvergent g s) :
-- imply
  HasLaplace (f - g) s (laplace f s - laplace g s) := by
-- proof
  refine ⟨?_, ?_⟩
  · simpa only [LaplaceConvergent, Pi.sub_apply, smul_sub] using! hf.sub hg
  · unfold laplace
    simp only [Pi.sub_apply, smul_sub]
    exact integral_sub hf hg

/--
[hasLaplace_const_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma hasLaplace_const_smul
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s c : ℂ}
-- given
  (hf : LaplaceConvergent f s) :
-- imply
  HasLaplace (fun t => c • f t) s (c • laplace f s) := by
-- proof
  refine ⟨hf.const_smul c, ?_⟩
  unfold laplace
  simp only [smul_comm _ c]
  exact Integrable.integral_smul c hf

/--
[LaplaceConvergent.mono_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma LaplaceConvergent.mono_re
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s w : ℂ}
-- given
  (hf : LaplaceConvergent f s)
  (hsw : s.re ≤ w.re) :
-- imply
  LaplaceConvergent f w := by
-- proof
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

/--
[LaplaceConvergent.exp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma LaplaceConvergent.exp_smul
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s a : ℂ} :
-- imply
  LaplaceConvergent (fun t => Complex.exp (a * (t : ℂ)) • f t) s ↔
    LaplaceConvergent f (s - a) := by
-- proof
  unfold LaplaceConvergent
  refine integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi
  change Complex.exp (-s * (t : ℂ)) • (Complex.exp (a * (t : ℂ)) • f t) =
    Complex.exp (-(s - a) * (t : ℂ)) • f t
  have hexp : (-s * (t : ℂ)) + (a * (t : ℂ)) = -(s - a) * (t : ℂ) := by
    ring
  rw [smul_smul, ← Complex.exp_add, hexp]

/--
[laplace_exp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma laplace_exp_smul
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s a : ℂ} :
-- imply
  laplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s =
    laplace f (s - a) := by
-- proof
  unfold laplace
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  change Complex.exp (-s * (t : ℂ)) • (Complex.exp (a * (t : ℂ)) • f t) =
    Complex.exp (-(s - a) * (t : ℂ)) • f t
  have hexp : (-s * (t : ℂ)) + (a * (t : ℂ)) = -(s - a) * (t : ℂ) := by
    ring
  rw [smul_smul, ← Complex.exp_add, hexp]

/--
[hasLaplace_exp_smul_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma hasLaplace_exp_smul_iff
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s a : ℂ}
  {v : E} :
-- imply
  HasLaplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s v ↔
    HasLaplace f (s - a) v := by
-- proof
  unfold HasLaplace
  rw [LaplaceConvergent.exp_smul, laplace_exp_smul]

/--
[hasLaplace_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
lemma hasLaplace_one
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {s : ℂ}
-- given
  (hs : 0 < s.re) :
-- imply
  HasLaplace (fun _ : ℝ => (1 : ℂ)) s s⁻¹ := by
-- proof
  refine ⟨?_, ?_⟩
  · unfold LaplaceConvergent
    simp only [smul_eq_mul, mul_one]
    exact integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0
  · unfold laplace
    simp only [smul_eq_mul, mul_one]
    rw [integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0]
    simp [div_eq_mul_inv]


-- created on 2026-10-20
-- updated on 2026-10-23
