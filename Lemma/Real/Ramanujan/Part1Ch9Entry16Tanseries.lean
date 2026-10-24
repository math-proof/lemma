import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry16Tanseries
open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries
open scoped BigOperators
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry16Tanseries


namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_cosSeries_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_cosSeries_summable (x : ℝ) :
  Summable (fun k : ℕ => (Nat.choose (2 * k) k : ℝ) * Real.cos x ^ (2 * k + 1) /
    ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))) := by
  have hcos : ‖Real.cos x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one x
  exact (summable_arcsinIntegralSeries_term (Real.cos x) hcos).congr (fun k => by
    rw [arcsinIntegralSeries_term_eq])

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_sinSeries_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_sinSeries_summable (x : ℝ) :
  Summable (fun k : ℕ => (Nat.choose (2 * k) k : ℝ) * Real.sin x ^ (2 * k + 1) /
    ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))) := by
  have hsin : ‖Real.sin x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one x
  exact (summable_arcsinIntegralSeries_term (Real.sin x) hsin).congr (fun k => by
    rw [arcsinIntegralSeries_term_eq])

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_sin_cos_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_sin_cos_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
  Real.sin θ ∈ Set.Ioo 0 1 ∧ Real.cos θ ∈ Set.Ioo 0 1 := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hθ
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith)
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin_ne : Real.sin θ ≠ 1 := by
    intro h
    have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h] at hsq
    nlinarith [hsq, hcos_pos, sq_nonneg (Real.cos θ)]
  have hcos_ne : Real.cos θ ≠ 1 := by
    intro h
    have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h] at hsq
    nlinarith [hsq, hsin_pos, sq_nonneg (Real.sin θ)]
  refine ⟨⟨hsin_pos, lt_of_le_of_ne (Real.sin_le_one θ) hsin_ne⟩,
    ⟨hcos_pos, lt_of_le_of_ne (Real.cos_le_one θ) hcos_ne⟩⟩

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_norm_ne_of_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_norm_ne_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
  ‖Real.sin θ‖ < 1 ∧ ‖Real.cos θ‖ < 1 ∧ Real.sin θ ≠ 0 ∧ Real.cos θ ≠ 0 := by
  have hmem := chap9_sin_cos_mem_Ioo hθ
  simp only [Set.mem_Ioo] at hmem
  have hsin_norm : ‖Real.sin θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hmem.1.1, hmem.1.2]
  have hcos_norm : ‖Real.cos θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hmem.2.1, hmem.2.2]
  exact ⟨hsin_norm, hcos_norm, ne_of_gt hmem.1.1, ne_of_gt hmem.2.1⟩

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_mem_pi_div_two_of_pi_div_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_mem_pi_div_two_of_pi_div_four {x : ℝ}
  (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
  x ∈ Set.Ioo 0 (Real.pi / 2) ∧ 2 * x ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hx ⊢
  constructor
  · constructor <;> linarith [hx.1, hx.2]
  · constructor <;> linarith [hx.1, hx.2]

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_arcsin_sin_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_arcsin_sin_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
  Real.arcsin (Real.sin θ) = θ := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hθ
  exact Real.arcsin_sin (by linarith) (by linarith)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_arcsin_cos_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_arcsin_cos_of_mem {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
  Real.arcsin (Real.cos x) = Real.pi / 2 - x := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hx
  have hmem : Real.pi / 2 - x ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [hx.1, hx.2]
  have hsin : Real.sin (Real.pi / 2 - x) = Real.cos x := Real.sin_pi_div_two_sub x
  have harcsin := chap9_arcsin_sin_of_mem hmem
  rwa [hsin] at harcsin

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9F_cos_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9F_cos_eq_tsum (x : ℝ) :
  arcsinIntegralSeries (Real.cos x) =
    ∑' k : ℕ, (Nat.choose (2 * k) k : ℝ) * Real.cos x ^ (2 * k + 1) /
      ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold arcsinIntegralSeries
  congr 1
  funext k
  exact arcsinIntegralSeries_term_eq k (Real.cos x)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9F_sin_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9F_sin_eq_tsum (x : ℝ) :
  arcsinIntegralSeries (Real.sin x) =
    ∑' k : ℕ, (Nat.choose (2 * k) k : ℝ) * Real.sin x ^ (2 * k + 1) /
      ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold arcsinIntegralSeries
  congr 1
  funext k
  exact arcsinIntegralSeries_term_eq k (Real.sin x)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9F_sin_two_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9F_sin_two_mul_eq (x : ℝ) :
  arcsinIntegralSeries (Real.sin (2 * x)) =
    ∑' k : ℕ, chapter9CentralSineTerm (2 * x) k :=
  chap9F_sin_eq_tsum (2 * x)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_diff_tsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_diff_tsum_eq (x : ℝ) :
  (∑' k : ℕ, chapter9Entry16DifferenceTerm x k) =
    arcsinIntegralSeries (Real.cos x) - arcsinIntegralSeries (Real.sin x) := by
  have hcosS := chap9_cosSeries_summable x
  have hsinS := chap9_sinSeries_summable x
  have hterm : (fun k : ℕ => chapter9Entry16DifferenceTerm x k) =
    (fun k : ℕ =>
      ((Nat.choose (2 * k) k : ℝ) * Real.cos x ^ (2 * k + 1) /
        ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))) -
      ((Nat.choose (2 * k) k : ℝ) * Real.sin x ^ (2 * k + 1) /
        ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)))) := by
    funext k
    unfold chapter9Entry16DifferenceTerm
    ring
  rw [hterm, hcosS.tsum_sub hsinS, ← chap9F_cos_eq_tsum, ← chap9F_sin_eq_tsum]

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_tan_cot_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_tan_cot_identity {x : ℝ} (hsin : Real.sin x ≠ 0)
  (hcos : Real.cos x ≠ 0) :
  Real.sin x / Real.cos x - Real.cos x / Real.sin x +
    2 * (Real.cos (2 * x) / Real.sin (2 * x)) = 0 := by
  have hsin2x : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x :=
    Real.sin_two_mul x
  have hcos2x : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 :=
    Real.cos_two_mul' x
  rw [hsin2x, hcos2x]
  field_simp
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_cos_pos_of_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_cos_pos_of_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
  0 < Real.cos x := by
  have hpi := Real.pi_pos
  rw [Set.mem_Icc] at hx
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_sin_cos_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_sin_cos_mem_Icc (t : ℝ) : Real.sin t ∈ Set.Icc (-1 : ℝ) 1 ∧
  Real.cos t ∈ Set.Icc (-1 : ℝ) 1 := by
  refine ⟨⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩,
    ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩⟩

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9H_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9H_continuousOn : ContinuousOn chap9H (Set.Icc 0 (Real.pi / 4)) := by
  have hF := continuousOn_arcsinIntegralSeries
  have hcos_on : ContinuousOn Real.cos (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuous_cos.continuousOn
  have hsin_on : ContinuousOn Real.sin (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuous_sin.continuousOn
  have hsin2_on : ContinuousOn (fun x : ℝ => Real.sin (2 * x))
    (Set.Icc 0 (Real.pi / 4)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hFcos : ContinuousOn (fun x : ℝ => arcsinIntegralSeries (Real.cos x))
    (Set.Icc 0 (Real.pi / 4)) :=
    hF.comp hcos_on (fun x _ => (chap9_sin_cos_mem_Icc x).2)
  have hFsin : ContinuousOn (fun x : ℝ => arcsinIntegralSeries (Real.sin x))
    (Set.Icc 0 (Real.pi / 4)) :=
    hF.comp hsin_on (fun x _ => (chap9_sin_cos_mem_Icc x).1)
  have hFsin2 : ContinuousOn (fun x : ℝ => arcsinIntegralSeries (Real.sin (2 * x)))
    (Set.Icc 0 (Real.pi / 4)) :=
    hF.comp hsin2_on (fun x _ => (chap9_sin_cos_mem_Icc (2 * x)).1)
  have h2cos_on : ContinuousOn (fun x : ℝ => 2 * Real.cos x)
    (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul hcos_on
  have hlog_on : ContinuousOn (fun x : ℝ => Real.log (2 * Real.cos x))
    (Set.Icc 0 (Real.pi / 4)) := by
    have hlog := Real.continuousOn_log
    refine hlog.comp h2cos_on (fun x hx => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hpos := chap9_cos_pos_of_mem_Icc hx
    linarith
  have h1 : ContinuousOn (fun x : ℝ =>
    arcsinIntegralSeries (Real.cos x) - arcsinIntegralSeries (Real.sin x) +
      (1 / 2 : ℝ) * arcsinIntegralSeries (Real.sin (2 * x)))
    (Set.Icc 0 (Real.pi / 4)) :=
    (hFcos.sub hFsin).add (continuousOn_const.mul hFsin2)
  have h2 : ContinuousOn (fun x : ℝ => (Real.pi / 2) * Real.log (2 * Real.cos x))
    (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul hlog_on
  have h := h1.sub h2
  unfold chap9H
  exact h

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_two_mul_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_two_mul_hasDerivAt (x : ℝ) :
  HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
  simpa using (hasDerivAt_id' x).const_mul (2 : ℝ)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_sin_two_mul_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_sin_two_mul_hasDerivAt (x : ℝ) :
  HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * x) * 2) x :=
  (Real.hasDerivAt_sin (2 * x)).comp x (chap9_two_mul_hasDerivAt x)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_Fcos_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_Fcos_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
  HasDerivAt (fun x : ℝ => arcsinIntegralSeries (Real.cos x))
    ((Real.arcsin (Real.cos x) / Real.cos x) * (-Real.sin x)) x := by
  have hmem := chap9_mem_pi_div_two_of_pi_div_four hx
  have hnorm := chap9_norm_ne_of_mem_Ioo hmem.1
  have houter := hasDerivAt_arcsinIntegralSeries hnorm.2.1 hnorm.2.2.2
  exact houter.comp x (Real.hasDerivAt_cos x)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_Fsin_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_Fsin_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
  HasDerivAt (fun x : ℝ => arcsinIntegralSeries (Real.sin x))
    ((Real.arcsin (Real.sin x) / Real.sin x) * Real.cos x) x := by
  have hmem := chap9_mem_pi_div_two_of_pi_div_four hx
  have hnorm := chap9_norm_ne_of_mem_Ioo hmem.1
  have houter := hasDerivAt_arcsinIntegralSeries hnorm.1 hnorm.2.2.1
  exact houter.comp x (Real.hasDerivAt_sin x)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_Fsin2_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_Fsin2_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
  HasDerivAt (fun x : ℝ => arcsinIntegralSeries (Real.sin (2 * x)))
    ((Real.arcsin (Real.sin (2 * x)) / Real.sin (2 * x)) *
      (Real.cos (2 * x) * 2)) x := by
  have hmem := chap9_mem_pi_div_two_of_pi_div_four hx
  have hnorm := chap9_norm_ne_of_mem_Ioo hmem.2
  have houter := hasDerivAt_arcsinIntegralSeries hnorm.1 hnorm.2.2.1
  exact houter.comp x (chap9_sin_two_mul_hasDerivAt x)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_log_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_log_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
  HasDerivAt (fun x : ℝ => Real.log (2 * Real.cos x))
    ((2 * Real.cos x)⁻¹ * (2 * (-Real.sin x))) x := by
  have hmem := chap9_mem_pi_div_two_of_pi_div_four hx
  have hcos_pos : 0 < Real.cos x := (chap9_sin_cos_mem_Ioo hmem.1).2.1
  have hne : 2 * Real.cos x ≠ 0 := ne_of_gt (by linarith)
  have houter := Real.hasDerivAt_log hne
  have hinner : HasDerivAt (fun x : ℝ => 2 * Real.cos x) (2 * (-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul 2
  exact houter.comp x hinner

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9H_hasDerivAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9H_hasDerivAt_zero {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
  HasDerivAt chap9H 0 x := by
  have hmem := chap9_mem_pi_div_two_of_pi_div_four hx
  have hnorm := chap9_norm_ne_of_mem_Ioo hmem.1
  have hsin_ne : Real.sin x ≠ 0 := hnorm.2.2.1
  have hcos_ne : Real.cos x ≠ 0 := hnorm.2.2.2
  have harcsin_sin := chap9_arcsin_sin_of_mem hmem.1
  have harcsin_cos := chap9_arcsin_cos_of_mem hx
  have harcsin_sin2 : Real.arcsin (Real.sin (2 * x)) = 2 * x :=
    chap9_arcsin_sin_of_mem hmem.2
  have hFcos := chap9_Fcos_hasDerivAt hx
  have hFsin := chap9_Fsin_hasDerivAt hx
  have hFsin2 := chap9_Fsin2_hasDerivAt hx
  have hlog := chap9_log_hasDerivAt hx
  have hhalf : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * arcsinIntegralSeries (Real.sin (2 * x)))
    ((1 / 2 : ℝ) *
      ((Real.arcsin (Real.sin (2 * x)) / Real.sin (2 * x)) *
        (Real.cos (2 * x) * 2))) x :=
    hFsin2.const_mul (1 / 2 : ℝ)
  have hlogpart : HasDerivAt
    (fun x : ℝ => (Real.pi / 2) * Real.log (2 * Real.cos x))
    ((Real.pi / 2) * ((2 * Real.cos x)⁻¹ * (2 * (-Real.sin x)))) x :=
    hlog.const_mul (Real.pi / 2)
  have h12 := hFcos.sub hFsin
  have h123 := h12.add hhalf
  have hH : HasDerivAt chap9H
    (((((Real.arcsin (Real.cos x) / Real.cos x) * (-Real.sin x)) -
      ((Real.arcsin (Real.sin x) / Real.sin x) * Real.cos x)) +
      ((1 / 2 : ℝ) *
        ((Real.arcsin (Real.sin (2 * x)) / Real.sin (2 * x)) *
          (Real.cos (2 * x) * 2)))) -
      ((Real.pi / 2) * ((2 * Real.cos x)⁻¹ * (2 * (-Real.sin x))))) x :=
    h123.sub hlogpart
  rw [harcsin_sin, harcsin_cos, harcsin_sin2] at hH
  have hsin2x : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x :=
    Real.sin_two_mul x
  have hcos2x : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 :=
    Real.cos_two_mul' x
  have hDzero : (((((Real.pi / 2 - x) / Real.cos x) * (-Real.sin x)) -
    ((x / Real.sin x) * Real.cos x)) +
    ((1 / 2 : ℝ) *
      (((2 * x) / Real.sin (2 * x)) * (Real.cos (2 * x) * 2)))) -
    ((Real.pi / 2) * ((2 * Real.cos x)⁻¹ * (2 * (-Real.sin x)))) = 0 := by
    rw [hsin2x, hcos2x]
    field_simp
    ring
  rwa [hDzero] at hH

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_sinc_pos_of_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_sinc_pos_of_mem_Icc {θ : ℝ}
  (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 < Real.sinc θ := by
  by_cases h0 : θ = 0
  · subst h0
    rw [Real.sinc_zero]
    norm_num
  · rw [Real.sinc_of_ne_zero h0]
    have hpi := Real.pi_pos
    rw [Set.mem_Icc] at hθ
    have hpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h0)
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
    exact div_pos hsin hpos

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9D_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9D_continuousOn :
  ContinuousOn chap9D (Set.Icc 0 (Real.pi / 2)) := by
  unfold chap9D
  exact Real.continuous_cos.continuousOn.div Real.continuous_sinc.continuousOn
    (fun θ hθ => ne_of_gt (chap9_sinc_pos_of_mem_Icc hθ))

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9D_eq_mul_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9D_eq_mul_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
  chap9D θ = θ * Real.cos θ / Real.sin θ := by
  unfold chap9D
  have hne : θ ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hθ).1
  rw [Real.sinc_of_ne_zero hne]
  have hsin_ne : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (Set.mem_Ioo.mp hθ).1 (by
      have hpi := Real.pi_pos
      have h2 := (Set.mem_Ioo.mp hθ).2
      linarith))
  field_simp

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9Phi_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9Phi_continuousOn :
  ContinuousOn chap9Phi (Set.Icc 0 (Real.pi / 2)) := by
  unfold chap9Phi
  exact continuousOn_arcsinIntegralSeries.comp Real.continuous_sin.continuousOn
    (fun θ _ => (chap9_sin_cos_mem_Icc θ).1)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9Phi_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9Phi_hasDerivAt {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
  HasDerivAt chap9Phi (chap9D θ) θ := by
  have hnorm := chap9_norm_ne_of_mem_Ioo hθ
  have houter := hasDerivAt_arcsinIntegralSeries hnorm.1 hnorm.2.2.1
  have hcomp : HasDerivAt (fun θ : ℝ => arcsinIntegralSeries (Real.sin θ))
    ((Real.arcsin (Real.sin θ) / Real.sin θ) * Real.cos θ) θ :=
    houter.comp θ (Real.hasDerivAt_sin θ)
  have harcsin := chap9_arcsin_sin_of_mem hθ
  rw [harcsin] at hcomp
  have hDeq : (θ / Real.sin θ) * Real.cos θ = chap9D θ := by
    rw [chap9D_eq_mul_div hθ]
    ring
  rwa [hDeq] at hcomp

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9Phi_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9Phi_integral_eq :
  (∫ θ in (0 : ℝ)..(Real.pi / 2), chap9D θ) = arcsinIntegralSeries 1 := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hcont := chap9Phi_continuousOn
  have hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
    HasDerivAt chap9Phi (chap9D θ) θ :=
    fun θ hθ => chap9Phi_hasDerivAt hθ
  have hint : IntervalIntegrable chap9D MeasureTheory.volume 0 (Real.pi / 2) :=
    chap9D_continuousOn.intervalIntegrable_of_Icc hle
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
    hderiv hint
  have hsin_pi2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have hPhi_pi2 : chap9Phi (Real.pi / 2) = arcsinIntegralSeries 1 := by
    unfold chap9Phi
    rw [hsin_pi2]
  have hPhi0 : chap9Phi 0 = 0 := by
    unfold chap9Phi
    rw [Real.sin_zero, arcsinIntegralSeries_zero]
  rwa [hPhi_pi2, hPhi0, sub_zero] at hFTC

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9_sin_eq_mul_sinc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9_sin_eq_mul_sinc (θ : ℝ) :
  Real.sin θ = θ * Real.sinc θ := by
  by_cases h0 : θ = 0
  · subst h0
    simp only [Real.sin_zero, Real.sinc_zero, zero_mul]
  · rw [Real.sinc_of_ne_zero h0]
    field_simp

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9A_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9A_hasDerivAt {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
  HasDerivAt chap9A (Real.log (Real.sin θ) + chap9D θ) θ := by
  have hsin_ne : Real.sin θ ≠ 0 :=
    (chap9_norm_ne_of_mem_Ioo hθ).2.2.1
  have hlogsin : HasDerivAt (fun θ : ℝ => Real.log (Real.sin θ))
    ((Real.sin θ)⁻¹ * Real.cos θ) θ :=
    (Real.hasDerivAt_log hsin_ne).comp θ (Real.hasDerivAt_sin θ)
  have hid : HasDerivAt (fun θ : ℝ => θ) 1 θ := hasDerivAt_id' θ
  have hprod : HasDerivAt (fun θ : ℝ => θ * Real.log (Real.sin θ))
    (1 * Real.log (Real.sin θ) + θ * ((Real.sin θ)⁻¹ * Real.cos θ)) θ :=
    hid.mul hlogsin
  have hDeq : 1 * Real.log (Real.sin θ) + θ * ((Real.sin θ)⁻¹ * Real.cos θ)
    = Real.log (Real.sin θ) + chap9D θ := by
    rw [chap9D_eq_mul_div hθ]
    ring
  rwa [hDeq] at hprod

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9A_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9A_continuousOn :
  ContinuousOn chap9A (Set.Icc 0 (Real.pi / 2)) := by
  have hB : ContinuousOn (fun θ : ℝ => θ * Real.log θ)
    (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_mul_log.continuousOn
  have hsinc_on : ContinuousOn Real.sinc (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_sinc.continuousOn
  have hlog_sinc_on : ContinuousOn (fun θ : ℝ => Real.log (Real.sinc θ))
    (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuousOn_log.comp hsinc_on (fun θ hθ => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (chap9_sinc_pos_of_mem_Icc hθ))
  have hC : ContinuousOn (fun θ : ℝ => θ * Real.log (Real.sinc θ))
    (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_id.mul hlog_sinc_on
  have hBC : ContinuousOn
    (fun θ : ℝ => θ * Real.log θ + θ * Real.log (Real.sinc θ))
    (Set.Icc 0 (Real.pi / 2)) :=
    hB.add hC
  have hEq : Set.EqOn chap9A
    (fun θ : ℝ => θ * Real.log θ + θ * Real.log (Real.sinc θ))
    (Set.Icc 0 (Real.pi / 2)) := by
    intro θ hθ
    unfold chap9A
    by_cases h0 : θ = 0
    · subst h0
      simp only [Real.sin_zero, Real.log_zero, Real.sinc_zero, Real.log_one,
        zero_mul, add_zero]
    · have hsinc_ne : Real.sinc θ ≠ 0 :=
      ne_of_gt (chap9_sinc_pos_of_mem_Icc hθ)
      have hsin_eq := chap9_sin_eq_mul_sinc θ
      have hlog : Real.log (Real.sin θ)
        = Real.log θ + Real.log (Real.sinc θ) := by
        rw [hsin_eq, Real.log_mul h0 hsinc_ne]
      rw [hlog, mul_add]
  exact hBC.congr hEq

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9A_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9A_integral_eq :
  (∫ θ in (0 : ℝ)..(Real.pi / 2),
    (Real.log (Real.sin θ) + chap9D θ)) = 0 := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hcont := chap9A_continuousOn
  have hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
    HasDerivAt chap9A (Real.log (Real.sin θ) + chap9D θ) θ :=
    fun θ hθ => chap9A_hasDerivAt hθ
  have hlog_int : IntervalIntegrable (fun θ : ℝ => Real.log (Real.sin θ))
    MeasureTheory.volume 0 (Real.pi / 2) :=
    intervalIntegrable_log_sin
  have hD_int : IntervalIntegrable chap9D MeasureTheory.volume 0 (Real.pi / 2) :=
    chap9D_continuousOn.intervalIntegrable_of_Icc hle
  have hint : IntervalIntegrable
    (fun θ : ℝ => Real.log (Real.sin θ) + chap9D θ)
    MeasureTheory.volume 0 (Real.pi / 2) :=
    hlog_int.add hD_int
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcont
    hderiv hint
  have hApi2 : chap9A (Real.pi / 2) = 0 := by
    unfold chap9A
    rw [Real.sin_pi_div_two, Real.log_one, mul_zero]
  have hA0 : chap9A 0 = 0 := by
    unfold chap9A
    rw [zero_mul]
  rwa [hApi2, hA0, sub_zero] at hFTC

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9F_one_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9F_one_eq : arcsinIntegralSeries 1 = (Real.pi / 2) * Real.log 2 := by
  have hpi := Real.pi_pos
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hlog_int : IntervalIntegrable (fun θ : ℝ => Real.log (Real.sin θ))
    MeasureTheory.volume 0 (Real.pi / 2) :=
    intervalIntegrable_log_sin
  have hD_int : IntervalIntegrable chap9D MeasureTheory.volume 0 (Real.pi / 2) :=
    chap9D_continuousOn.intervalIntegrable_of_Icc hle
  have hadd := intervalIntegral.integral_add hlog_int hD_int
  have hA0 := chap9A_integral_eq
  have hPhi := chap9Phi_integral_eq
  have hlog_val : (∫ x in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin x))
    = -Real.log 2 * Real.pi / 2 :=
    integral_log_sin_zero_pi_div_two
  rw [hadd] at hA0
  rw [hlog_val, hPhi] at hA0
  linarith [hA0]

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9H_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9H_zero : chap9H 0 = 0 := by
  have hF1 := chap9F_one_eq
  unfold chap9H
  rw [Real.cos_zero, Real.sin_zero, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero,
    mul_one, arcsinIntegralSeries_zero, hF1]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[chap9H_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
private lemma chap9H_eq_zero {x : ℝ} (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
  chap9H x = 0 := by
  rw [Set.mem_Icc] at hx
  have hsub : Set.Icc 0 x ⊆ Set.Icc 0 (Real.pi / 4) := by
    intro y hy
    rw [Set.mem_Icc] at hy ⊢
    constructor <;> linarith [hy.1, hy.2, hx.2]
  have hcont : ContinuousOn chap9H (Set.Icc 0 x) :=
    chap9H_continuousOn.mono hsub
  have hderiv : ∀ y ∈ Set.Ioo 0 x, HasDerivAt chap9H 0 y := by
    intro y hy
    rw [Set.mem_Ioo] at hy
    have hymem : y ∈ Set.Ioo 0 (Real.pi / 4) := by
      rw [Set.mem_Ioo]
      constructor <;> linarith [hy.1, hy.2, hx.2]
    exact chap9H_hasDerivAt_zero hymem
  have hint : IntervalIntegrable (fun _ => (0 : ℝ)) MeasureTheory.volume 0 x :=
    intervalIntegrable_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hcont
    hderiv hint
  simp only [intervalIntegral.integral_const, smul_zero, chap9H_zero,
    sub_zero] at hFTC
  exact hFTC.symm

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry16Tanseries

/--
[ramanujan_part1_ch9_entry16_tanseries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tanseries.lean)
-/
@[path]
lemma ramanujan_part1_ch9_entry16_tanseries
  {x : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hxUpper : x ≤ Real.pi / 4) :
-- imply
  0 < 2 * Real.cos x ∧
    Summable (chapter9Entry16DifferenceTerm x) ∧
    Summable (chapter9CentralSineTerm (2 * x)) ∧
    (∑' k : ℕ, chapter9Entry16DifferenceTerm x k) =
    Real.pi / 2 * Real.log (2 * Real.cos x) -
    (1 / 2 : ℝ) * ∑' k : ℕ, chapter9CentralSineTerm (2 * x) k := by
-- proof
  have hpi := Real.pi_pos
  have hcos_pos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hcosS := chap9_cosSeries_summable x
  have hsinS := chap9_sinSeries_summable x
  have hdiffS : Summable (chapter9Entry16DifferenceTerm x) :=
    (hcosS.sub hsinS).congr (fun k => by
      unfold chapter9Entry16DifferenceTerm
      ring)
  have hcentralS : Summable (chapter9CentralSineTerm (2 * x)) :=
    (chap9_sinSeries_summable (2 * x)).congr (fun k => by rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · exact hdiffS
  · exact hcentralS
  · have hxIcc : x ∈ Set.Icc 0 (Real.pi / 4) := ⟨hx0, hxUpper⟩
    have hH := chap9H_eq_zero hxIcc
    have hdiff := chap9_diff_tsum_eq x
    have hcent := chap9F_sin_two_mul_eq x
    unfold chap9H at hH
    rw [hdiff, ← hcent]
    linear_combination hH
end



-- created on 2026-10-20
-- updated on 2026-10-23
