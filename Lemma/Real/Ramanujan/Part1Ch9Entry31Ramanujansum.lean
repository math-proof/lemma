import Mathlib
import sympy.Basic
import Def.Analysis.Ramanujan.Part1Ch9Entry31Ramanujansum
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry31Ramanujansum


namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[ak_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma ak_le_one (k : ℕ) : (Nat.choose (2 * k) k : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 := by
  have h := Nat.centralBinom_le_four_pow k
  have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hcast : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (4 : ℝ) ^ k := by
    exact_mod_cast h
  rw [← h4]
  have hpos : (0 : ℝ) < 4 ^ k := by positivity
  rwa [div_le_one hpos]

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[psi_norm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma psi_norm_bound (y : ℝ) (k : ℕ) :
  ‖chapter9PsiTerm y k‖ ≤ 1 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  unfold chapter9PsiTerm
  have hdpos : (0 : ℝ) < (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hsin : |Real.sin (Real.pi * y) ^ (2 * k + 1)| ≤ 1 := by
    calc |Real.sin (Real.pi * y) ^ (2 * k + 1)|
      = |Real.sin (Real.pi * y)| ^ (2 * k + 1) := by rw [abs_pow]
      _ ≤ 1 ^ (2 * k + 1) := by
        apply pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one _) _
      _ = 1 := one_pow _
  have hak := ak_le_one k
  have hak_abs : |(Nat.choose (2 * k) k : ℝ) / (2 : ℝ) ^ (2 * k)| ≤ 1 := by
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ (Nat.choose (2*k) k : ℝ) / (2:ℝ)^(2*k))]
  have heq : (Nat.choose (2 * k) k : ℝ) * Real.sin (Real.pi * y) ^ (2*k+1) /
    ((2:ℝ)^(2*k) * (((2*k+1 : ℕ):ℝ)^2))
    = ((Nat.choose (2*k) k : ℝ) / (2:ℝ)^(2*k)) *
      (Real.sin (Real.pi * y) ^ (2*k+1)) / (((2*k+1 : ℕ):ℝ)^2) := by
    field_simp
  rw [heq, Real.norm_eq_abs, abs_div, abs_mul]
  have h1 : |(Nat.choose (2*k) k : ℝ) / (2:ℝ)^(2*k)| * |Real.sin (Real.pi * y)^(2*k+1)| ≤ 1 := by
    calc |(Nat.choose (2*k) k : ℝ) / (2:ℝ)^(2*k)| * |Real.sin (Real.pi * y)^(2*k+1)|
      ≤ 1 * 1 := by
        apply mul_le_mul hak_abs hsin (abs_nonneg _) (by linarith [hak_abs])
      _ = 1 := one_mul 1
  calc |(Nat.choose (2*k) k : ℝ) / (2:ℝ)^(2*k)| *
    |Real.sin (Real.pi * y)^(2*k+1)| / |(((2*k+1 : ℕ):ℝ)^2)|
    ≤ 1 / |(((2*k+1 : ℕ):ℝ)^2)| := by
      apply div_le_div_of_nonneg_right h1 (by positivity)
    _ = 1 / (((2*k+1 : ℕ):ℝ)^2) := by rw [abs_of_pos hdpos]

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[summ_shift_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma summ_shift_sq : Summable (fun k : ℕ => 1 / ((((k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) := by
    rw [Real.summable_one_div_nat_pow]
    norm_num
  have hinj : Function.Injective (fun k : ℕ => k + 1) := Nat.succ_injective
  have h := h2.comp_injective hinj
  have heq :
    (fun k : ℕ => 1 / ((((k + 1 : ℕ)) : ℝ) ^ 2)) =
      ((fun n : ℕ => 1 / ((n : ℝ) ^ 2)) ∘ (fun k : ℕ => k + 1)) := by
    funext k
    simp [Function.comp, Nat.cast_add, Nat.cast_one]
  rwa [heq]

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[summ_odd_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma summ_odd_sq : Summable (fun k : ℕ => 1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) summ_shift_sq
  have hle : ((((k + 1 : ℕ)) : ℝ)) ≤ ((((2 * k + 1 : ℕ)) : ℝ)) := by
    have h : k + 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast h
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hle 2)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[psi_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma psi_summable (y : ℝ) : Summable (chapter9PsiTerm y) :=
  Summable.of_norm_bounded summ_odd_sq (psi_norm_bound y)

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[psi_eq_centralSine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma psi_eq_centralSine (y : ℝ) (k : ℕ) :
  chapter9PsiTerm y k =
    Entry16Tanseries.chapter9CentralSineTerm (Real.pi * y) k := by
  rfl

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[diff_eq_psi_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
private lemma diff_eq_psi_sub (x : ℝ) (k : ℕ) :
  Entry16Tanseries.chapter9Entry16DifferenceTerm (Real.pi * x) k =
    chapter9PsiTerm (1 / 2 - x) k - chapter9PsiTerm x k := by
  unfold Entry16Tanseries.chapter9Entry16DifferenceTerm chapter9PsiTerm
  have hsin : Real.sin (Real.pi * (1 / 2 - x)) = Real.cos (Real.pi * x) := by
    have harg : Real.pi * (1 / 2 - x) = Real.pi / 2 - Real.pi * x := by ring
    rw [harg, Real.sin_pi_div_two_sub]
  rw [hsin]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry31Ramanujansum

/--
[ramanujan_part1_ch9_entry31_ramanujansum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry31Ramanujansum.lean)
-/
@[path]
lemma ramanujan_part1_ch9_entry31_ramanujansum
  {x : ℝ}
-- given
  (hxLower : 0 ≤ x)
  (hxUpper : x ≤ 1 / 4) :
-- imply
  Summable (chapter9PsiTerm (1 / 2 - x)) ∧
    Summable (chapter9PsiTerm (2 * x)) ∧
    Summable (chapter9PsiTerm x) ∧
    0 < 2 * Real.cos (Real.pi * x) ∧
    (∑' k : ℕ, chapter9PsiTerm (1 / 2 - x) k) +
    (1 / 2 : ℝ) * ∑' k : ℕ, chapter9PsiTerm (2 * x) k -
    ∑' k : ℕ, chapter9PsiTerm x k =
    Real.pi / 2 * Real.log (2 * Real.cos (Real.pi * x)) := by
-- proof
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpx0 : 0 ≤ Real.pi * x := mul_nonneg hpi.le hxLower
  have hpxU : Real.pi * x ≤ Real.pi / 4 := by
    have h := mul_le_mul_of_nonneg_left hxUpper hpi.le
    have heq : Real.pi * (1 / 4 : ℝ) = Real.pi / 4 := by ring
    rwa [heq] at h
  obtain ⟨hcos, -, -, hEq⟩ :=
    Entry16Tanseries.ramanujan_part1_ch9_entry16_tanseries (Real.pi * x) hpx0 hpxU
  have hS1 : Summable (chapter9PsiTerm (1 / 2 - x)) := psi_summable _
  have hS2 : Summable (chapter9PsiTerm (2 * x)) := psi_summable _
  have hS3 : Summable (chapter9PsiTerm x) := psi_summable _
  have htsub : (∑' k : ℕ,
    Entry16Tanseries.chapter9Entry16DifferenceTerm (Real.pi * x) k) =
    (∑' k : ℕ, chapter9PsiTerm (1 / 2 - x) k) -
      ∑' k : ℕ, chapter9PsiTerm x k := by
    rw [tsum_congr (diff_eq_psi_sub x), Summable.tsum_sub hS1 hS3]
  have hcent : (∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm
    (2 * (Real.pi * x)) k) = ∑' k : ℕ, chapter9PsiTerm (2 * x) k := by
    have harg : 2 * (Real.pi * x) = Real.pi * (2 * x) := by ring
    rw [harg]
    exact tsum_congr fun k => (psi_eq_centralSine (2 * x) k).symm
  refine ⟨hS1, hS2, hS3, hcos, ?_⟩
  rw [htsub, hcent] at hEq
  linear_combination hEq
end



-- created on 2026-10-20
-- updated on 2026-10-23
