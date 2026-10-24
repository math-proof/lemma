import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.RiemannXi
open critical strip `0 < s.re < 1` (the left half follows by reflecting
open RiemannXi


namespace RiemannXi

/--
[differentiable_riemannXi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma differentiable_riemannXi
  :
-- imply
  Differentiable ℂ riemannXi := by
-- proof
  have h1 : Differentiable ℂ (fun s : ℂ => s * (s - 1) / 2) := by fun_prop
  have h2 := h1.mul differentiable_completedZeta₀
  have h3 := h2.add_const (1 / 2 : ℂ)
  unfold riemannXi
  exact h3

end RiemannXi

namespace RiemannXi

/--
[riemannXi_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma riemannXi_one_sub
  {s : ℂ} :
-- imply
  riemannXi (1 - s) = riemannXi s := by
-- proof
  unfold riemannXi
  have hfactor : (1 - s) * ((1 - s) - 1) / 2 = s * (s - 1) / 2 := by ring
  rw [hfactor, completedRiemannZeta₀_one_sub]

end RiemannXi

namespace RiemannXi

/--
[riemannXi_eq_mul_completedRiemannZeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma riemannXi_eq_mul_completedRiemannZeta
  {s : ℂ}
-- given
  (hs0 : s ≠ 0)
  (hs1 : s ≠ 1) :
-- imply
  riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
-- proof
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold riemannXi
  rw [completedRiemannZeta_eq]
  field_simp
  ring

end RiemannXi

namespace RiemannXi

/--
[riemannXi_ne_zero_of_one_le_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma riemannXi_ne_zero_of_one_le_re
  {s : ℂ}
-- given
  (hs : 1 ≤ s.re) :
-- imply
  riemannXi s ≠ 0 := by
-- proof
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  obtain rfl | hs1 := eq_or_ne s 1
  · have hval : riemannXi 1 = 1 / 2 := by simp [riemannXi]
    rw [hval]
    norm_num
  · have hzeta := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_completedRiemannZeta₀ hs0] at hzeta
    have hN : completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) ≠ 0 :=
      fun hN => hzeta (by rw [hN, zero_div])
    have hfac : s * (s - 1) / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero
    have hag := riemannXi_eq_mul_completedRiemannZeta hs0 hs1
    rw [completedRiemannZeta_eq] at hag
    rw [hag]
    exact mul_ne_zero hfac hN

end RiemannXi

namespace RiemannXi

/--
[re_pos_of_riemannXi_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma re_pos_of_riemannXi_eq_zero
  {s : ℂ}
-- given
  (h : riemannXi s = 0) :
-- imply
  0 < s.re := by
-- proof
  by_contra hle
  push Not at hle
  have h1 : 1 ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hne := riemannXi_ne_zero_of_one_le_re h1
  rw [riemannXi_one_sub] at hne
  exact hne h

end RiemannXi

namespace RiemannXi

/--
[re_lt_one_of_riemannXi_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma re_lt_one_of_riemannXi_eq_zero
  {s : ℂ}
-- given
  (h : riemannXi s = 0) :
-- imply
  s.re < 1 := by
-- proof
  by_contra hle
  push Not at hle
  exact riemannXi_ne_zero_of_one_le_re hle h

end RiemannXi

namespace RiemannXi

/--
[riemannXi_mem_strip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma riemannXi_mem_strip
  {s : ℂ}
-- given
  (h : riemannXi s = 0) :
-- imply
  0 < s.re ∧ s.re < 1 :=
-- proof
  ⟨re_pos_of_riemannXi_eq_zero h, re_lt_one_of_riemannXi_eq_zero h⟩

end RiemannXi

namespace RiemannXi

/--
[riemannXi_entire_functional_equation_and_critical_strip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
lemma riemannXi_entire_functional_equation_and_critical_strip
  :
-- imply
  Differentiable ℂ riemannXi ∧
    (∀ s : ℂ, riemannXi (1 - s) = riemannXi s) ∧
    ∀ s : ℂ, riemannXi s = 0 → 0 < s.re ∧ s.re < 1 :=
-- proof
  ⟨differentiable_riemannXi, riemannXi_one_sub,
    fun _s h => riemannXi_mem_strip h⟩

end RiemannXi


-- created on 2026-10-20
-- updated on 2026-10-23
