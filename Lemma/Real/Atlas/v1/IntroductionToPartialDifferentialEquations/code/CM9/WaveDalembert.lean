import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM9.WaveDalembert
open Real Set MeasureTheory intervalIntegral CM9 CM9.Wave


namespace CM9.Wave

/--
[hasDerivAt_comp_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma hasDerivAt_comp_add_right
  {f : ℝ → ℝ}
  {x t : ℝ}
-- given
  (hF : DifferentiableAt ℝ f (x + t)) :
-- imply
  HasDerivAt (fun s => f (x + s)) (deriv f (x + t)) t := by
-- proof
  have h1 : HasDerivAt (fun s => x + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add x
  exact (hF.hasDerivAt.comp t h1).congr_deriv (by ring)

end CM9.Wave

namespace CM9.Wave

/--
[hasDerivAt_comp_sub_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma hasDerivAt_comp_sub_right
  {f : ℝ → ℝ}
  {x t : ℝ}
-- given
  (hF : DifferentiableAt ℝ f (x - t)) :
-- imply
  HasDerivAt (fun s => f (x - s)) (-deriv f (x - t)) t := by
-- proof
  have h1 : HasDerivAt (fun s => x - s) (-1) t := by
    have := (hasDerivAt_id t).const_sub x
    simp at this; exact this
  have h2 := hF.hasDerivAt.comp t h1
  convert h2 using 1; ring

end CM9.Wave

namespace CM9.Wave

/--
[hasDerivAt_comp_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma hasDerivAt_comp_add_left
  {f : ℝ → ℝ}
  {x t : ℝ}
-- given
  (hF : DifferentiableAt ℝ f (t + x)) :
-- imply
  HasDerivAt (fun s => f (s + x)) (deriv f (t + x)) t := by
-- proof
  have h1 : HasDerivAt (fun s => s + x) 1 t := by
    simpa using (hasDerivAt_id t).add_const x
  exact (hF.hasDerivAt.comp t h1).congr_deriv (by ring)

end CM9.Wave

namespace CM9.Wave

/--
[hasDerivAt_comp_sub_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma hasDerivAt_comp_sub_left
  {f : ℝ → ℝ}
  {x t : ℝ}
-- given
  (hF : DifferentiableAt ℝ f (t - x)) :
-- imply
  HasDerivAt (fun s => f (s - x)) (deriv f (t - x)) t := by
-- proof
  have h1 : HasDerivAt (fun s => s - x) 1 t := by
    simpa using (hasDerivAt_id t).sub_const x
  exact (hF.hasDerivAt.comp t h1).congr_deriv (by ring)

end CM9.Wave

namespace CM9.Wave

/--
[differentiable_of_contDiff2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma differentiable_of_contDiff2
  {f : ℝ → ℝ}
-- given
  (hf : ContDiff ℝ 2 f) :
-- imply
  Differentiable ℝ f :=
-- proof
  hf.differentiable (by norm_num)

end CM9.Wave

namespace CM9.Wave

/--
[differentiable_deriv_of_contDiff2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma differentiable_deriv_of_contDiff2
  {f : ℝ → ℝ}
-- given
  (hf : ContDiff ℝ 2 f) :
-- imply
  Differentiable ℝ (deriv f) :=
-- proof
  hf.differentiable_deriv_two

end CM9.Wave

namespace CM9.Wave

/--
[contDiff_antideriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma contDiff_antideriv
  {g : ℝ → ℝ}
-- given
  (hg : ContDiff ℝ 1 g) :
-- imply
  ContDiff ℝ 2 (fun z => ∫ y in (0 : ℝ)..z, g y) := by
-- proof
  have hg_cont : Continuous g := hg.continuous
  have key : ContDiff ℝ (1 + 1) (fun z => ∫ y in (0 : ℝ)..z, g y) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (hg_cont.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
    · intro h; simp at h
    · have hderiv : deriv (fun z => ∫ y in (0 : ℝ)..z, g y) = g := by
      ext z
      exact (hg_cont.integral_hasStrictDerivAt 0 z).hasDerivAt.deriv
      rwa [hderiv]
  exact_mod_cast key

end CM9.Wave

namespace CM9.Wave

/--
[general_solution_satisfies_wave_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma general_solution_satisfies_wave_eq
  {F G : ℝ → ℝ}
-- given
  (hF : ContDiff ℝ 2 F)
  (hG : ContDiff ℝ 2 G) :
-- imply
  ∀ t x : ℝ, deriv (fun t' => deriv (fun t'' => F (x + t'') + G (x - t'')) t') t = deriv (fun x' => deriv (fun x'' => F (x'' + t) + G (x'' - t)) x') x := by
-- proof
  intro t x
  have hFd : Differentiable ℝ F := differentiable_of_contDiff2 hF
  have hGd : Differentiable ℝ G := differentiable_of_contDiff2 hG
  have hFd' : Differentiable ℝ (deriv F) := differentiable_deriv_of_contDiff2 hF
  have hGd' : Differentiable ℝ (deriv G) := differentiable_deriv_of_contDiff2 hG
  have hdt : ∀ t', HasDerivAt (fun t'' => F (x + t'') + G (x - t''))
    (deriv F (x + t') - deriv G (x - t')) t' := by
    intro t'
    have h1 := hasDerivAt_comp_add_right (hFd.differentiableAt (x := x + t'))
    have h2 := hasDerivAt_comp_sub_right (hGd.differentiableAt (x := x - t'))
    have h3 := h1.add h2
    convert h3 using 1
  have hdt_eq : (fun t' => deriv (fun t'' => F (x + t'') + G (x - t'')) t') =
    fun t' => deriv F (x + t') - deriv G (x - t') := by
    ext t'; exact (hdt t').deriv
  have hdtt : HasDerivAt (fun t' => deriv F (x + t') - deriv G (x - t'))
    (deriv (deriv F) (x + t) + deriv (deriv G) (x - t)) t := by
    have h1 := hasDerivAt_comp_add_right (hFd'.differentiableAt (x := x + t))
    have h2 := hasDerivAt_comp_sub_right (hGd'.differentiableAt (x := x - t))
    convert h1.sub h2 using 1; ring
  have hdx : ∀ x', HasDerivAt (fun x'' => F (x'' + t) + G (x'' - t))
    (deriv F (x' + t) + deriv G (x' - t)) x' := by
    intro x'
    have h1 := hasDerivAt_comp_add_left (hFd.differentiableAt (x := x' + t))
    have h2 := hasDerivAt_comp_sub_left (hGd.differentiableAt (x := x' - t))
    have h3 := h1.add h2
    convert h3 using 1
  have hdx_eq : (fun x' => deriv (fun x'' => F (x'' + t) + G (x'' - t)) x') =
    fun x' => deriv F (x' + t) + deriv G (x' - t) := by
    ext x'; exact (hdx x').deriv
  have hdxx : HasDerivAt (fun x' => deriv F (x' + t) + deriv G (x' - t))
    (deriv (deriv F) (x + t) + deriv (deriv G) (x - t)) x :=
    (hasDerivAt_comp_add_left (hFd'.differentiableAt (x := x + t))).add
      (hasDerivAt_comp_sub_left (hGd'.differentiableAt (x := x - t)))
  rw [hdt_eq, hdtt.deriv, hdx_eq, hdxx.deriv]

end CM9.Wave

namespace CM9.Wave

/--
[dAlembert_regularity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma dAlembert_regularity
  {f g : ℝ → ℝ}
-- given
  (hf : ContDiff ℝ 2 f)
  (hg : ContDiff ℝ 1 g) :
-- imply
  ContDiff ℝ 2 (fun p : ℝ × ℝ => dAlembertFormula f g p.1 p.2) := by
-- proof
  have hg_cont : Continuous g := hg.continuous
  set G := fun z => ∫ y in (0 : ℝ)..z, g y
  have hG : ContDiff ℝ 2 G := contDiff_antideriv g hg
  have hG_deriv : ∀ z, HasDerivAt G (g z) z := by
    intro z; exact (hg_cont.integral_hasStrictDerivAt 0 z).hasDerivAt
  set Fp : ℝ → ℝ := fun z => (1/2 : ℝ) * f z + (1/2) * G z
  set Fm : ℝ → ℝ := fun z => (1/2 : ℝ) * f z - (1/2) * G z
  have hFp : ContDiff ℝ 2 Fp := (hf.const_smul (1/2 : ℝ)).add (hG.const_smul (1/2 : ℝ))
  have hFm : ContDiff ℝ 2 Fm := (hf.const_smul (1/2 : ℝ)).sub (hG.const_smul (1/2 : ℝ))
  have integral_eq : ∀ a b : ℝ, ∫ z in a..b, g z = G b - G a := by
    intro a b
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _ => hG_deriv z) (hg_cont.intervalIntegrable _ _)
  have h_eq : (fun p : ℝ × ℝ => dAlembertFormula f g p.1 p.2) =
    fun p : ℝ × ℝ => Fp (p.2 + p.1) + Fm (p.2 - p.1) := by
    ext ⟨t, x⟩
    simp only [dAlembertFormula, Fp, Fm, integral_eq]
    ring
  rw [h_eq]
  exact (hFp.comp (contDiff_snd.add contDiff_fst)).add
    (hFm.comp (contDiff_snd.sub contDiff_fst))

end CM9.Wave

namespace CM9.Wave

/--
[wave_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma wave_uniqueness
  {u₁ u₂ : ℝ → ℝ → ℝ}
-- given
  (h₁_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₁ p.1 p.2))
  (h₁_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u₁ t'' x) t') t = deriv (fun x' => deriv (fun x'' => u₁ t x'') x') x)
  (h₂_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u₂ p.1 p.2))
  (h₂_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u₂ t'' x) t') t = deriv (fun x' => deriv (fun x'' => u₂ t x'') x') x)
  (h_pos : ∀ x, u₁ 0 x = u₂ 0 x)
  (h_vel : ∀ x, deriv (fun t => u₁ t x) 0 = deriv (fun t => u₂ t x) 0) :
-- imply
  ∀ t x, u₁ t x = u₂ t x := by
-- proof
  intro t x
  have h := WaveEquation1D.zero_wave_is_zero (fun t x => u₁ t x - u₂ t x)
    (h₁_reg.sub h₂_reg)
    (WaveEquation1D.wave_eq_of_sub u₁ u₂ h₁_reg h₂_reg h₁_wave h₂_wave)
    (fun x => by simp [h_pos x])
    (WaveEquation1D.deriv_sub_zero u₁ u₂ h₁_reg h₂_reg h_vel)
    t x
  linarith

end CM9.Wave

namespace CM9.Wave

/--
[wave_null_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma wave_null_decomposition
  {u : ℝ → ℝ → ℝ}
-- given
  (hu_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2))
  (hu_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u t'' x) t') t = deriv (fun x' => deriv (fun x'' => u t x'') x') x) :
-- imply
  ∃ F G : ℝ → ℝ, ContDiff ℝ 2 F ∧ ContDiff ℝ 2 G ∧ (∀ t x, u t x = F (x + t) + G (x - t)) := by
-- proof
  set U := fun p : ℝ × ℝ => u p.1 p.2
  set f₀ : ℝ → ℝ := fun x => u 0 x
  set g₀ : ℝ → ℝ := fun x => deriv (fun t => u t x) 0
  have hf₀_C2 : ContDiff ℝ 2 f₀ :=
    show ContDiff ℝ 2 (U ∘ (Prod.mk 0)) from hu_reg.comp (contDiff_prodMk_right 0)
  have hg₀_C1 : ContDiff ℝ 1 g₀ := by
    have hU_diff : Differentiable ℝ U := hu_reg.differentiable (by norm_num)
    have key : g₀ = fun x => fderiv ℝ U (0, x) (1, 0) := funext fun x =>
      (((hU_diff (0, x)).hasFDerivAt.comp (0 : ℝ)
        ((hasFDerivAt_id 0).prodMk (hasFDerivAt_const x 0))).hasDerivAt
        |> fun h => (by convert h using 1 : HasDerivAt (fun t => u t x) _ 0)).deriv
    rw [key]
    exact ((hu_reg.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).comp
      (contDiff_prodMk_right 0)).clm_apply contDiff_const
  have hg₀_cont : Continuous g₀ := hg₀_C1.continuous
  set G_int : ℝ → ℝ := fun z => ∫ y in (0 : ℝ)..z, g₀ y
  have hG_int_C2 : ContDiff ℝ 2 G_int := contDiff_antideriv g₀ hg₀_C1
  have hG_int_deriv : ∀ z, HasDerivAt G_int (g₀ z) z :=
    fun z => (hg₀_cont.integral_hasStrictDerivAt 0 z).hasDerivAt
  set F : ℝ → ℝ := fun z => f₀ z / 2 + G_int z / 2
  set G_fun : ℝ → ℝ := fun z => f₀ z / 2 - G_int z / 2
  have hF_C2 : ContDiff ℝ 2 F := (hf₀_C2.div_const 2).add (hG_int_C2.div_const 2)
  have hG_C2 : ContDiff ℝ 2 G_fun := (hf₀_C2.div_const 2).sub (hG_int_C2.div_const 2)
  refine ⟨F, G_fun, hF_C2, hG_C2, ?_⟩
  set v : ℝ → ℝ → ℝ := fun t x => F (x + t) + G_fun (x - t)
  have hv_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => v p.1 p.2) :=
    (hF_C2.comp (contDiff_snd.add contDiff_fst)).add (hG_C2.comp (contDiff_snd.sub contDiff_fst))
  have hv_wave := general_solution_satisfies_wave_eq F G_fun hF_C2 hG_C2
  have h_pos : ∀ x, u 0 x = v 0 x := by
    intro x; show f₀ x = F (x + 0) + G_fun (x - 0)
    simp only [add_zero, sub_zero]
    show f₀ x = f₀ x / 2 + G_int x / 2 + (f₀ x / 2 - G_int x / 2); ring
  have h_vel : ∀ x, deriv (fun t => u t x) 0 = deriv (fun t => v t x) 0 := by
    intro x
    have hFd : Differentiable ℝ F := hF_C2.differentiable (by norm_num)
    have hGd : Differentiable ℝ G_fun := hG_C2.differentiable (by norm_num)
    have hF_at : HasDerivAt (fun t => F (x + t)) (deriv F x) 0 := by
      have := hasDerivAt_comp_add_right (hFd.differentiableAt (x := x + 0))
      simp only [add_zero] at this; exact this
    have hG_at : HasDerivAt (fun t => G_fun (x - t)) (-deriv G_fun x) 0 := by
      have := hasDerivAt_comp_sub_right (hGd.differentiableAt (x := x - 0))
      simp only [sub_zero] at this; exact this
    have hv_deriv : HasDerivAt (fun t => v t x) (deriv F x - deriv G_fun x) 0 := by
      show HasDerivAt (fun t => F (x + t) + G_fun (x - t)) _ 0
      convert hF_at.add hG_at using 1
    rw [hv_deriv.deriv]
    have hf₀d : Differentiable ℝ f₀ := hf₀_C2.differentiable (by norm_num)
    have hF_hd : HasDerivAt F (deriv f₀ x / 2 + g₀ x / 2) x :=
      ((hf₀d x).hasDerivAt.div_const 2).add ((hG_int_deriv x).div_const 2)
    have hG_hd : HasDerivAt G_fun (deriv f₀ x / 2 - g₀ x / 2) x :=
      ((hf₀d x).hasDerivAt.div_const 2).sub ((hG_int_deriv x).div_const 2)
    rw [hF_hd.deriv, hG_hd.deriv]; ring
  exact wave_uniqueness u v hu_reg hu_wave hv_reg hv_wave h_pos h_vel

end CM9.Wave

namespace CM9.Wave

/--
[hasDerivAt_F_of_null_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma hasDerivAt_F_of_null_decomp
  {f g F G : ℝ → ℝ}
-- given
  (hf : ContDiff ℝ 2 f)
  (_hg : ContDiff ℝ 1 g)
  (hFd : Differentiable ℝ F)
  (hFG_init_pos : ∀ x, F x + G x = f x)
  (hFG_init_vel : ∀ x, HasDerivAt (fun t => F (x + t) + G (x - t)) (g x) 0) :
-- imply
  ∀ x, HasDerivAt F ((deriv f x + g x) / 2) x := by
-- proof
  intro x
  have hGd : Differentiable ℝ G := by
    have hG_eq : G = fun y => f y - F y := funext fun y => by linarith [hFG_init_pos y]
    rw [hG_eq]; exact (hf.differentiable (by norm_num)).sub hFd
  have h1 : HasDerivAt (fun t => F (x + t)) (deriv F x) 0 := by
    have ha : HasDerivAt (fun t => x + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add x
    have hb : HasDerivAt F (deriv F x) (x + 0) := by rw [add_zero]; exact (hFd x).hasDerivAt
    exact (hb.comp 0 ha).congr_deriv (by ring)
  have h2 : HasDerivAt (fun t => G (x - t)) (-deriv G x) 0 := by
    have ha : HasDerivAt (fun t => x - t) (-1) 0 := by
      have := (hasDerivAt_id (0 : ℝ)).const_sub x; simp at this; exact this
    have hb : HasDerivAt G (deriv G x) (x - 0) := by rw [sub_zero]; exact (hGd x).hasDerivAt
    exact (hb.comp 0 ha).congr_deriv (by ring)
  have h_vel : deriv F x - deriv G x = g x := by
    have h_sum := h1.add h2
    linarith [h_sum.unique (hFG_init_vel x)]
  have h_pos : deriv F x + deriv G x = deriv f x := by
    have hG_eq : G = fun y => f y - F y := funext fun y => by linarith [hFG_init_pos y]
    linarith [show deriv G x = deriv f x - deriv F x by
      rw [hG_eq]; exact deriv_sub (hf.differentiable (by norm_num) x) (hFd x)]
  rw [show (deriv f x + g x) / 2 = deriv F x by linarith]
  exact (hFd x).hasDerivAt

end CM9.Wave

namespace CM9.Wave

/--
[null_decomposition_determines_dAlembert](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma null_decomposition_determines_dAlembert
  {f g : ℝ → ℝ}
  {F G : ℝ → ℝ}
-- given
  (hf : ContDiff ℝ 2 f)
  (hg : ContDiff ℝ 1 g)
  (hFd : Differentiable ℝ F)
  (hFG_init_pos : ∀ x, F x + G x = f x)
  (hFG_init_vel : ∀ x, HasDerivAt (fun t => F (x + t) + G (x - t)) (g x) 0) :
-- imply
  ∀ t x, F (x + t) + G (x - t) = dAlembertFormula f g t x := by
-- proof
  have hF_hasderiv := hasDerivAt_F_of_null_decomp f g F G hf hg hFd hFG_init_pos hFG_init_vel
  intro t x
  have hGG : ∀ y, G y = f y - F y := fun y => by linarith [hFG_init_pos y]
  rw [hGG (x - t)]
  suffices h : F (x + t) - F (x - t) =
    ((f (x + t) - f (x - t)) / 2 + (∫ y in (x - t)..(x + t), g y) / 2) by
    simp only [dAlembertFormula]; linarith
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg_cont : Continuous g := hg.continuous
  have ftc_F : ∫ y in (x - t)..(x + t), (fun y => (deriv f y + g y) / 2) y =
    F (x + t) - F (x - t) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF_hasderiv y)
      ((((hf.continuous_deriv (by norm_num)).add hg_cont).div_const _).intervalIntegrable _ _)
  have ftc_f : ∫ y in (x - t)..(x + t), deriv f y = f (x + t) - f (x - t) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => (hf_diff y).hasDerivAt)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable _ _)
  rw [← ftc_F]
  have hint_df : IntervalIntegrable (deriv f) volume (x - t) (x + t) :=
    (hf.continuous_deriv (by norm_num)).intervalIntegrable _ _
  have hint_g : IntervalIntegrable g volume (x - t) (x + t) :=
    hg_cont.intervalIntegrable _ _
  have h_split : ∫ y in (x - t)..(x + t), (deriv f y + g y) / 2 =
    (∫ y in (x - t)..(x + t), deriv f y) / 2 +
    (∫ y in (x - t)..(x + t), g y) / 2 := by
    have : (fun y => (deriv f y + g y) / 2) =
      fun y => (1/2 : ℝ) * deriv f y + (1/2 : ℝ) * g y := by ext y; ring
    rw [this, intervalIntegral.integral_add (hint_df.const_mul _) (hint_g.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [h_split, ftc_f]

end CM9.Wave

namespace CM9.Wave

/--
[dAlembert_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM9/WaveDalembert.lean)
-/
@[path]
lemma dAlembert_uniqueness
  {f g : ℝ → ℝ}
  {u : ℝ → ℝ → ℝ}
-- given
  (hf : ContDiff ℝ 2 f)
  (hg : ContDiff ℝ 1 g)
  (hu_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2))
  (hu_wave : ∀ t x, deriv (fun t' => deriv (fun t'' => u t'' x) t') t = deriv (fun x' => deriv (fun x'' => u t x'') x') x)
  (hu_init_pos : ∀ x, u 0 x = f x)
  (hu_init_vel : ∀ x, HasDerivAt (fun t => u t x) (g x) 0) :
-- imply
  ∀ t x, u t x = dAlembertFormula f g t x := by
-- proof
  obtain ⟨F, G, hF_reg, _hG_reg, hFG⟩ := wave_null_decomposition u hu_reg hu_wave
  have hFd : Differentiable ℝ F := hF_reg.differentiable (by norm_num)
  have h_init_pos : ∀ x, F x + G x = f x := by
    intro x
    have h := hFG 0 x
    simp [add_zero, sub_zero] at h
    linarith [hu_init_pos x]
  have h_init_vel : ∀ x, HasDerivAt (fun t => F (x + t) + G (x - t)) (g x) 0 := by
    intro x
    have heq : (fun t => u t x) = (fun t => F (x + t) + G (x - t)) := by
      ext t; linarith [hFG t x]
    exact heq ▸ hu_init_vel x
  have h_dalembert := null_decomposition_determines_dAlembert f g F G hf hg hFd h_init_pos h_init_vel
  intro t x
  rw [hFG t x]
  exact h_dalembert t x

end CM9.Wave


-- created on 2026-10-23
