import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.JInvariantTwist
open WeierstrassCurve Polynomial


/--
[algebraMap_AlgClosure_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
lemma algebraMap_AlgClosure_ne_zero
  {k : Type u}
  [Field k]
  {a : k}
-- given
  (ha : a ≠ 0) :
-- imply
  algebraMap k (AlgebraicClosure k) a ≠ 0 := by
-- proof
  intro h
  exact ha (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k) (by rwa [map_zero]))

/--
[lemma_26_9_cross_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
lemma lemma_26_9_cross_identity
  {k : Type u}
  [Field k]
  {a₄ a₆ a₄' a₆' : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (h3 : (3 : k) ≠ 0)
  (hΔ : 4 * a₄ ^ 3 + 27 * a₆ ^ 2 ≠ 0)
  (hΔ' : 4 * a₄' ^ 3 + 27 * a₆' ^ 2 ≠ 0)
  (hj : 1728 * (4 * a₄ ^ 3) / (4 * a₄ ^ 3 + 27 * a₆ ^ 2) = 1728 * (4 * a₄' ^ 3) / (4 * a₄' ^ 3 + 27 * a₆' ^ 2)) :
-- imply
  a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3 := by
-- proof
  have h1 : 1728 * (4 * a₄ ^ 3) * (4 * a₄' ^ 3 + 27 * a₆' ^ 2) =
    1728 * (4 * a₄' ^ 3) * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
    rw [div_eq_div_iff hΔ hΔ'] at hj; exact hj
  have h2' : (186624 : k) * (a₄ ^ 3 * a₆' ^ 2 - a₄' ^ 3 * a₆ ^ 2) = 0 := by
    linear_combination h1
  have h186 : (186624 : k) ≠ 0 := by
    have : (186624 : k) = 2 ^ 8 * 3 ^ 6 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have h4 : a₄ ^ 3 * a₆' ^ 2 - a₄' ^ 3 * a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp h2').resolve_left h186
  linear_combination h4

variable {k : Type u} [Field k]
/--
[a₄'_ne_zero_of_generic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
identity forces $a_4' \neq 0$. -/
lemma a₄'_ne_zero_of_generic (a₄ a₆ a₄' a₆' : k)
  (ha₄ : a₄ ≠ 0) (_ha₆ : a₆ ≠ 0)
  (hΔ' : 4 * a₄' ^ 3 + 27 * a₆' ^ 2 ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
  a₄' ≠ 0 := by
  intro h
  rw [h, zero_pow (by omega : 3 ≠ 0), mul_zero] at hcross
  have : a₆' = 0 := by
    obtain h1 | h1 := mul_eq_zero.mp hcross
    · exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h1
    · exact absurd (pow_eq_zero_iff (by omega : 3 ≠ 0) |>.mp h1) ha₄
  simp [h, this] at hΔ'

variable {k : Type u} [Field k]
/--
[a₆'_ne_zero_of_generic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
identity forces $a_6' \neq 0$. -/
lemma a₆'_ne_zero_of_generic (a₄ a₆ a₄' a₆' : k)
  (_ha₄ : a₄ ≠ 0) (ha₆ : a₆ ≠ 0)
  (hΔ' : 4 * a₄' ^ 3 + 27 * a₆' ^ 2 ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
  a₆' ≠ 0 := by
  intro h
  rw [h, zero_pow (by omega : 2 ≠ 0), zero_mul] at hcross
  have : a₄' = 0 := by
    obtain h1 | h1 := mul_eq_zero.mp hcross.symm
    · exact absurd (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h1) ha₆
    · exact pow_eq_zero_iff (by omega : 3 ≠ 0) |>.mp h1
  simp [h, this] at hΔ'

variable {k : Type u} [Field k]
/--
[a₆'_zero_of_a₆_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
lemma a₆'_zero_of_a₆_zero (a₄ a₆ a₄' a₆' : k)
  (ha₆ : a₆ = 0) (ha₄ : a₄ ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
  a₆' = 0 := by
  rw [ha₆, zero_pow (by omega : 2 ≠ 0), zero_mul] at hcross
  obtain h | h := mul_eq_zero.mp hcross
  · exact pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h
  · exact absurd (pow_eq_zero_iff (by omega : 3 ≠ 0) |>.mp h) ha₄

variable {k : Type u} [Field k]
/--
[a₄'_zero_of_a₄_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
lemma a₄'_zero_of_a₄_zero (a₄ a₆ a₄' a₆' : k)
  (ha₄ : a₄ = 0) (ha₆ : a₆ ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
  a₄' = 0 := by
  rw [ha₄, zero_pow (by omega : 3 ≠ 0), mul_zero] at hcross
  obtain h | h := mul_eq_zero.mp hcross.symm
  · exact absurd (pow_eq_zero_iff (by omega : 2 ≠ 0) |>.mp h) ha₆
  · exact pow_eq_zero_iff (by omega : 3 ≠ 0) |>.mp h

/--
[lemma_26_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
lemma lemma_26_9
  {k : Type u}
  [Field k]
  {a₄ a₆ a₄' a₆' : k}
-- given
  (h2 : (2 : k) ≠ 0)
  (h3 : (3 : k) ≠ 0)
  (hΔ : 4 * a₄ ^ 3 + 27 * a₆ ^ 2 ≠ 0)
  (hΔ' : 4 * a₄' ^ 3 + 27 * a₆' ^ 2 ≠ 0)
  (hj : 1728 * (4 * a₄ ^ 3) / (4 * a₄ ^ 3 + 27 * a₆ ^ 2) = 1728 * (4 * a₄' ^ 3) / (4 * a₄' ^ 3 + 27 * a₆' ^ 2)) :
-- imply
  ∃ (l : AlgebraicClosure k), l ≠ 0 ∧ algebraMap k (AlgebraicClosure k) a₄' = l ^ 4 * algebraMap k (AlgebraicClosure k) a₄ ∧ algebraMap k (AlgebraicClosure k) a₆' = l ^ 6 * algebraMap k (AlgebraicClosure k) a₆ := by
-- proof
  set ι := algebraMap k (AlgebraicClosure k) with hι_def
  have hcross := lemma_26_9_cross_identity a₄ a₆ a₄' a₆' h2 h3 hΔ hΔ' hj
  by_cases ha₆ : a₆ = 0
  ·
    have ha₄ : a₄ ≠ 0 := by intro h; simp [h, ha₆] at hΔ
    have ha₆' := a₆'_zero_of_a₆_zero a₄ a₆ a₄' a₆' ha₆ ha₄ hcross
    have ha₄' : a₄' ≠ 0 := by intro h; simp [h, ha₆'] at hΔ'
    obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq (ι a₄' / ι a₄) (by norm_num : 0 < 4)
    refine ⟨l, ?_, ?_, ?_⟩
    ·
      intro h0; rw [h0, zero_pow (by norm_num : 4 ≠ 0)] at hl
      exact div_ne_zero (algebraMap_AlgClosure_ne_zero a₄' ha₄')
        (algebraMap_AlgClosure_ne_zero a₄ ha₄) hl.symm
    ·
      rw [eq_div_iff (algebraMap_AlgClosure_ne_zero a₄ ha₄)] at hl; exact hl.symm
    ·
      simp [ha₆, ha₆']
  · by_cases ha₄ : a₄ = 0
    ·
      have ha₄' := a₄'_zero_of_a₄_zero a₄ a₆ a₄' a₆' ha₄ ha₆ hcross
      have ha₆' : a₆' ≠ 0 := by intro h; simp [h, ha₄'] at hΔ'
      obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq (ι a₆' / ι a₆) (by norm_num : 0 < 6)
      refine ⟨l, ?_, ?_, ?_⟩
      ·
        intro h0; rw [h0, zero_pow (by norm_num : 6 ≠ 0)] at hl
        exact div_ne_zero (algebraMap_AlgClosure_ne_zero a₆' ha₆')
          (algebraMap_AlgClosure_ne_zero a₆ ha₆) hl.symm
      ·
        simp [ha₄, ha₄']
      ·
        rw [eq_div_iff (algebraMap_AlgClosure_ne_zero a₆ ha₆)] at hl; exact hl.symm
    ·
      have ha₄' := a₄'_ne_zero_of_generic a₄ a₆ a₄' a₆' ha₄ ha₆ hΔ' hcross
      have ha₆' := a₆'_ne_zero_of_generic a₄ a₆ a₄' a₆' ha₄ ha₆ hΔ' hcross
      have hcross' : ι a₆' ^ 2 * ι a₄ ^ 3 = ι a₆ ^ 2 * ι a₄' ^ 3 := by
        have := congr_arg ι hcross; simp only [map_mul, map_pow] at this; exact this
      obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq
        (ι a₆' * ι a₄ / (ι a₆ * ι a₄')) (by norm_num : 0 < 2)
      have hι_a₄ := algebraMap_AlgClosure_ne_zero a₄ ha₄
      have hι_a₆ := algebraMap_AlgClosure_ne_zero a₆ ha₆
      have hι_a₄' := algebraMap_AlgClosure_ne_zero a₄' ha₄'
      have hι_a₆' := algebraMap_AlgClosure_ne_zero a₆' ha₆'
      have hl_ne : l ≠ 0 := by
        intro h0; rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hl
        exact div_ne_zero (mul_ne_zero hι_a₆' hι_a₄) (mul_ne_zero hι_a₆ hι_a₄') hl.symm
      have hl2 : l ^ 2 * (ι a₆ * ι a₄') = ι a₆' * ι a₄ := by
        rw [eq_div_iff (mul_ne_zero hι_a₆ hι_a₄')] at hl; exact hl
      refine ⟨l, hl_ne, ?_, ?_⟩
      ·
        have hl2_sq : (l ^ 2 * (ι a₆ * ι a₄')) ^ 2 = (ι a₆' * ι a₄) ^ 2 := by rw [hl2]
        have hl2_sq' : l ^ 4 * ι a₆ ^ 2 * ι a₄' ^ 2 = ι a₆' ^ 2 * ι a₄ ^ 2 := by
          linear_combination hl2_sq
        have key : l ^ 4 * ι a₄ * (ι a₆ ^ 2 * ι a₄' ^ 2) =
          ι a₄' * (ι a₆ ^ 2 * ι a₄' ^ 2) := by
          linear_combination ι a₄ * hl2_sq' + hcross'
        exact (mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ hι_a₆)
          (pow_ne_zero _ hι_a₄')) key).symm
      ·
        have hl2_cubed : (l ^ 2 * (ι a₆ * ι a₄')) ^ 3 = (ι a₆' * ι a₄) ^ 3 := by rw [hl2]
        have hl2_cubed' : l ^ 6 * ι a₆ ^ 3 * ι a₄' ^ 3 = ι a₆' ^ 3 * ι a₄ ^ 3 := by
          linear_combination hl2_cubed
        have key : l ^ 6 * ι a₆ * (ι a₆ ^ 2 * ι a₄' ^ 3) =
          ι a₆' * (ι a₆ ^ 2 * ι a₄' ^ 3) := by
          calc l ^ 6 * ι a₆ * (ι a₆ ^ 2 * ι a₄' ^ 3)
            = l ^ 6 * ι a₆ ^ 3 * ι a₄' ^ 3 := by ring
            _ = ι a₆' ^ 3 * ι a₄ ^ 3 := hl2_cubed'
            _ = ι a₆' * (ι a₆' ^ 2 * ι a₄ ^ 3) := by ring
            _ = ι a₆' * (ι a₆ ^ 2 * ι a₄' ^ 3) := by rw [hcross']
        exact (mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ hι_a₆)
          (pow_ne_zero _ hι_a₄')) key).symm

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
private lemma a_eq
  {k : Type u}
  [Field k]
  {a₄ a₆ a₄' a₆' : k}
-- given
  (ha₄ : a₄ ≠ 0)
  (_ha₆ : a₆ ≠ 0)
  (hΔ' : 4 * a₄' ^ 3 + 27 * a₆' ^ 2 ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
-- imply
  a₄' ≠ 0 := by
-- proof
  apply a a₄ a₆ a₄' a₆' ha₄ _ha₆ hΔ' hcross

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
private lemma a_eq_2
  {k : Type u}
  [Field k]
  {a₄ a₆ a₄' a₆' : k}
-- given
  (_ha₄ : a₄ ≠ 0)
  (ha₆ : a₆ ≠ 0)
  (hΔ' : 4 * a₄' ^ 3 + 27 * a₆' ^ 2 ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
-- imply
  a₆' ≠ 0 := by
-- proof
  apply a a₄ a₆ a₄' a₆' _ha₄ ha₆ hΔ' hcross

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
private lemma a_eq_3
  {k : Type u}
  [Field k]
  {a₄ a₆ a₄' a₆' : k}
-- given
  (ha₆ : a₆ = 0)
  (ha₄ : a₄ ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
-- imply
  a₆' = 0 := by
-- proof
  apply a a₄ a₆ a₄' a₆' ha₆ ha₄ hcross

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariantTwist.lean)
-/
@[path]
private lemma a_eq_4
  {k : Type u}
  [Field k]
  {a₄ a₆ a₄' a₆' : k}
-- given
  (ha₄ : a₄ = 0)
  (ha₆ : a₆ ≠ 0)
  (hcross : a₆' ^ 2 * a₄ ^ 3 = a₆ ^ 2 * a₄' ^ 3) :
-- imply
  a₄' = 0 := by
-- proof
  apply a a₄ a₆ a₄' a₆' ha₄ ha₆ hcross


-- created on 2026-10-23
