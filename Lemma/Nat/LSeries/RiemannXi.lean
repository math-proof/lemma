import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.RiemannXi
open critical strip `0 < s.re < 1` (the left half follows by reflecting
open RiemannXi


/--
[differentiable_riemannXi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma differentiable_riemannXi_eq
  :
-- imply
  Differentiable ℂ riemannXi := by
-- proof
  apply RiemannXi.differentiable_riemannXi

/--
[riemannXi_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma riemannXi_one_sub_eq
  {s : ℂ} :
-- imply
  riemannXi (1 - s) = riemannXi s := by
-- proof
  apply RiemannXi.riemannXi_one_sub s

/--
[riemannXi_eq_mul_completedRiemannZeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma riemannXi_eq_mul_completedRiemannZeta_eq
  {s : ℂ}
-- given
  (hs0 : s ≠ 0)
  (hs1 : s ≠ 1) :
-- imply
  riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
-- proof
  apply RiemannXi.riemannXi_eq_mul_completedRiemannZeta hs0 hs1

/--
[riemannXi_ne_zero_of_one_le_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma riemannXi_ne_zero_of_one_le_re_eq
  {s : ℂ}
-- given
  (hs : 1 ≤ s.re) :
-- imply
  riemannXi s ≠ 0 := by
-- proof
  apply RiemannXi.riemannXi_ne_zero_of_one_le_re hs

/--
[re_pos_of_riemannXi_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma re_pos_of_riemannXi_eq_zero_eq
  {s : ℂ}
-- given
  (h : riemannXi s = 0) :
-- imply
  0 < s.re := by
-- proof
  apply RiemannXi.re_pos_of_riemannXi_eq_zero h

/--
[re_lt_one_of_riemannXi_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma re_lt_one_of_riemannXi_eq_zero_eq
  {s : ℂ}
-- given
  (h : riemannXi s = 0) :
-- imply
  s.re < 1 := by
-- proof
  apply RiemannXi.re_lt_one_of_riemannXi_eq_zero h

/--
[riemannXi_mem_strip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma riemannXi_mem_strip_eq
  {s : ℂ}
-- given
  (h : riemannXi s = 0) :
-- imply
  0 < s.re ∧ s.re < 1 := by
-- proof
  apply RiemannXi.riemannXi_mem_strip h

/--
[riemannXi_entire_functional_equation_and_critical_strip](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/RiemannXi.lean)
-/
@[path]
private lemma riemannXi_entire_functional_equation_and_critical_strip_eq
  :
-- imply
  Differentiable ℂ riemannXi ∧
    (∀ s : ℂ, riemannXi (1 - s) = riemannXi s) ∧
    ∀ s : ℂ, riemannXi s = 0 → 0 < s.re ∧ s.re < 1 := by
-- proof
  apply RiemannXi.riemannXi_entire_functional_equation_and_critical_strip


-- created on 2026-10-20
