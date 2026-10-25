import Mathlib
import sympy.Basic
import Def.NumberTheory.Ramanujan.Part1Ch3Entry1SeriesTransformation
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry1SeriesTransformation


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

/--
[iterDeriv_comp_fun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
private lemma iterDeriv_comp_fun (j k : ℕ) (f : ℂ → ℂ) :
  iteratedDeriv k (iteratedDeriv j f) = iteratedDeriv (j + k) f := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    have hAdd : j + k + 1 = j + (k + 1) := by omega
    rw [iteratedDeriv_succ, ih, ← iteratedDeriv_succ, hAdd]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

/--
[analytic_diffIter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
private lemma analytic_diffIter (R₁ : ℝ) (f : ℂ → ℂ)
  (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁)) (j : ℕ) :
  DifferentiableOn ℂ (iteratedDeriv j f) (Metric.ball (0 : ℂ) R₁) := by
  have hU : UniqueDiffOn ℂ (Metric.ball (0 : ℂ) R₁) := Metric.isOpen_ball.uniqueDiffOn
  have hC : ContDiffOn ℂ (⊤ : WithTop ℕ∞) f (Metric.ball (0 : ℂ) R₁) := hf.contDiffOn hU
  have hDw : DifferentiableOn ℂ (iteratedDerivWithin j f (Metric.ball (0 : ℂ) R₁))
    (Metric.ball (0 : ℂ) R₁) :=
    hC.differentiableOn_iteratedDerivWithin (by simp) hU
  refine hDw.congr (fun x hx => ?_)
  exact (iteratedDerivWithin_eq_iteratedDeriv hU
    ((hC.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le le_top) hx).symm

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

/--
[rowHasSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
private lemma rowHasSum (R₁ : ℝ) (hR₁ : 1 < R₁) (f : ℂ → ℂ)
  (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁)) (Q : ℕ → ℂ) (j : ℕ) :
  HasSum (fun k : ℕ => Q j * iteratedDeriv (j + k) f 0 / (Nat.factorial k : ℂ))
    (Q j * iteratedDeriv j f 1) := by
  have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R₁ := by
    rwa [Metric.mem_ball, dist_zero_right, norm_one]
  have hT := Complex.hasSum_taylorSeries_on_ball (analytic_diffIter R₁ f hf j) h1mem
  have hEq : ∀ k : ℕ, Q j * (((Nat.factorial k : ℂ))⁻¹ • ((1 : ℂ) - 0) ^ k •
    iteratedDeriv k (iteratedDeriv j f) 0)
    = Q j * iteratedDeriv (j + k) f 0 / (Nat.factorial k : ℂ) := by
    intro k
    have hdk : iteratedDeriv k (iteratedDeriv j f) 0 = iteratedDeriv (j + k) f 0 :=
      congrFun (iterDeriv_comp_fun j k f) 0
    rw [hdk]
    simp only [sub_zero, one_pow, smul_eq_mul, one_mul]
    ring
  exact (hT.mul_left (Q j)).congr_fun (fun k => (hEq k).symm)

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

/--
[fibSum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
private lemma fibSum_eq (Q : ℕ → ℂ) (f : ℂ → ℂ) (n : ℕ) :
  (∑' q : {p : ℕ × ℕ // p.1 + p.2 = n},
    Q q.val.1 * iteratedDeriv (q.val.1 + q.val.2) f 0 / (Nat.factorial q.val.2 : ℂ))
  = (∑ j ∈ Finset.range (n + 1), Q j / (Nat.factorial (n - j) : ℂ)) *
    iteratedDeriv n f 0 := by
  have hStep1 : (∑' q : {p : ℕ × ℕ // p.1 + p.2 = n},
    Q q.val.1 * iteratedDeriv (q.val.1 + q.val.2) f 0 / (Nat.factorial q.val.2 : ℂ))
    = ∑ x : Fin (n + 1), Q x.val * iteratedDeriv (x.val + (n - x.val)) f 0 /
      (Nat.factorial (n - x.val) : ℂ) := by
    have hTs := (fibEquiv n).tsum_eq (fun q : {p : ℕ × ℕ // p.1 + p.2 = n} =>
      Q q.val.1 * iteratedDeriv (q.val.1 + q.val.2) f 0 / (Nat.factorial q.val.2 : ℂ))
    rw [tsum_fintype] at hTs
    rw [← hTs]
    apply Finset.sum_congr rfl
    intro x _
    rfl
  rw [hStep1, Fin.sum_univ_eq_sum_range (fun j => Q j * iteratedDeriv (j + (n - j)) f 0 /
    (Nat.factorial (n - j) : ℂ)) (n + 1), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := by
    have hmem := Finset.mem_range.mp hj
    omega
  have hjn : j + (n - j) = n := Nat.add_sub_cancel' hjle
  rw [hjn]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

/--
[ramanujan_part1_ch3_entry1_series_transformation_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry1_series_transformation_general
  {R₁ : ℝ}
  {f : ℂ → ℂ}
  {Q : ℕ → ℂ}
-- given
  (hR₁ : 1 < R₁)
  (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁))
  (hSumm : Summable (fun p : ℕ × ℕ => Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) / ((Nat.factorial p.2 : ℂ)))) :
-- imply
  ∃ v : ℂ,
    HasSum (fun n : ℕ => (∑ j ∈ Finset.range (n + 1), Q j / ((Nat.factorial (n - j) : ℂ))) *
    iteratedDeriv n f (0 : ℂ)) v ∧
    HasSum (fun n : ℕ => Q n * iteratedDeriv n f (1 : ℂ)) v := by
-- proof
  refine ⟨∑' p : ℕ × ℕ, Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) /
    ((Nat.factorial p.2 : ℂ)), ?_, ?_⟩
  · have hFib := hSumm.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 + p.2)
    exact hFib.congr_fun (fun n => (fibSum_eq Q f n).symm)
  · exact HasSum.prod_fiberwise hSumm.hasSum (fun j => rowHasSum R₁ hR₁ f hf Q j)
set_option linter.unusedVariables false in

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation

/--
[ramanujan_part1_ch3_entry1_series_transformation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry1_series_transformation
  {R₁ : ℝ}
  {f : ℂ → ℂ}
  {Q : ℕ → ℂ}
-- given
  (hR₁ : 1 < R₁)
  (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁))
  (hQ : ∃ R₂ : ℝ, 0 < R₂ ∧ ∀ z : ℂ, ‖z‖ < R₂ → Summable (fun n : ℕ => Q n * z ^ n))
  (hSumm : Summable (fun p : ℕ × ℕ => Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) / ((Nat.factorial p.2 : ℂ)))) :
-- imply
  ∃ v : ℂ,
    HasSum (fun n : ℕ => (∑ j ∈ Finset.range (n + 1), Q j / ((Nat.factorial (n - j) : ℂ))) *
    iteratedDeriv n f (0 : ℂ)) v ∧
    HasSum (fun n : ℕ => Q n * iteratedDeriv n f (1 : ℂ)) v := by
-- proof
apply ramanujan_part1_ch3_entry1_series_transformation_general <;> assumption

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation


-- created on 2026-10-20
-- updated on 2026-10-23
