import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.AbsoluteValues
open AbsoluteValueOnField


namespace AbsoluteValueOnField

/--
[nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma nonneg
  [Field k]
  {v : AbsoluteValueOnField k}
  {x : k} :
-- imply
  0 ≤ v x :=
-- proof
  AbsoluteValue.nonneg v x

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma eq_zero_iff
  [Field k]
  {v : AbsoluteValueOnField k}
  {x : k} :
-- imply
  v x = 0 ↔ x = 0 :=
-- proof
  AbsoluteValue.eq_zero v

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[thm_5_3c_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma thm_5_3c_forward
  [Field k]
  {v : AbsoluteValueOnField k}
  {n : ℕ}
-- given
  (hna : IsNonarchimedean (v : k → ℝ)) :
-- imply
  v (n : k) ≤ 1 := by
-- proof
  rw [show (n : k) = n • (1 : k) from by simp]
  exact le_trans hna.nsmul_le (le_of_eq v.map_one)

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[binomial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma binomial_bound
  [Field k]
  {v : AbsoluteValueOnField k}
  {x y : k}
  {n : ℕ}
-- given
  (hv : ∀ n : ℕ, v (n : k) ≤ 1) :
-- imply
  v (x + y) ^ n ≤ ((n : ℝ) + 1) * max (v x) (v y) ^ n := by
-- proof
  rw [show v (x + y) ^ n = v ((x + y) ^ n) from (map_pow v _ n).symm]
  rw [(Commute.all x y).add_pow n]
  calc v (∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m))
    ≤ ∑ m ∈ Finset.range (n + 1), v (x ^ m * y ^ (n - m) * ↑(n.choose m)) :=
      v.sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (n + 1), max (v x) (v y) ^ n := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mem_range] at hm
      simp only [map_mul, map_pow]
      calc v x ^ m * v y ^ (n - m) * v (↑(n.choose m))
        ≤ v x ^ m * v y ^ (n - m) * 1 := by gcongr; exact hv _
        _ = v x ^ m * v y ^ (n - m) := mul_one _
        _ ≤ max (v x) (v y) ^ m * max (v x) (v y) ^ (n - m) := by
          apply mul_le_mul
          · exact pow_le_pow_left₀ (v.nonneg x) (le_max_left _ _) m
          · exact pow_le_pow_left₀ (v.nonneg y) (le_max_right _ _) (n - m)
          · positivity
          · positivity
        _ = max (v x) (v y) ^ n := by rw [← pow_add]; congr 1; omega
    _ = ((n : ℝ) + 1) * max (v x) (v y) ^ n := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[le_of_pow_le_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma le_of_pow_le_mul_pow
  [Field k]
  {v : AbsoluteValueOnField k}
  {r M : ℝ}
-- given
  (hM : 0 ≤ M)
  (h : ∀ n : ℕ, r ^ n ≤ ((n : ℝ) + 1) * M ^ n) :
-- imply
  r ≤ M := by
-- proof
  by_contra hlt
  push Not at hlt
  obtain rfl | hM_pos := eq_or_lt_of_le hM
  · have h1 := h 1; simp at h1; linarith
  · have hrM : 1 < r / M := by rwa [one_lt_div₀ hM_pos]
    have key : ∀ n : ℕ, (r / M) ^ n ≤ (n : ℝ) + 1 := by
      intro n; rw [div_pow, div_le_iff₀ (pow_pos hM_pos n)]; exact h n
    obtain ⟨m, hm⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt hrM
    exact not_le.mpr hm (key m)

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[thm_5_3c_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma thm_5_3c_backward
  [Field k]
  {v : AbsoluteValueOnField k}
-- given
  (hv : ∀ n : ℕ, v (n : k) ≤ 1) :
-- imply
  IsNonarchimedean (v : k → ℝ) := by
-- proof
  intro x y
  exact le_of_pow_le_mul_pow (v (x + y)) (max (v x) (v y))
    (le_max_of_le_left (v.nonneg x)) (binomial_bound v hv x y)

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[thm_5_3c](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma thm_5_3c
  [Field k]
  {v : AbsoluteValueOnField k} :
-- imply
  IsNonarchimedean (v : k → ℝ) ↔ ∀ n : ℕ, v (n : k) ≤ 1 :=
-- proof
  ⟨thm_5_3c_forward v, thm_5_3c_backward v⟩

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[eq_one_of_pow_eq_one_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma eq_one_of_pow_eq_one_of_pos
  [Field k]
  {v : AbsoluteValueOnField k}
  {a : ℝ}
  {n : ℕ}
-- given
  (ha : 0 < a)
  (hn : n ≠ 0)
  (h : a ^ n = 1) :
-- imply
  a = 1 := by
-- proof
  by_contra hne
  obtain hlt | hgt := ne_iff_lt_or_gt.mp hne
  · exact absurd h (ne_of_lt (by simpa using pow_lt_pow_left₀ hlt ha.le hn))
  · exact absurd h (ne_of_gt (by simpa using pow_lt_pow_left₀ hgt (by linarith) hn))

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[natCast_pow_charP](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma natCast_pow_charP
  [Field k]
  {v : AbsoluteValueOnField k}
  {p : ℕ}
  [CharP k p]
  [Fact (Nat.Prime p)]
  {n : ℕ} :
-- imply
  (n : k) ^ p = (n : k) := by
-- proof
  haveI : ExpChar k p := expChar_prime k p
  rw [← frobenius_def p (n : k)]
  exact map_natCast (frobenius k p) n

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[natCast_pow_char_sub_one_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma natCast_pow_char_sub_one_eq_one
  [Field k]
  {v : AbsoluteValueOnField k}
  {p : ℕ}
  [CharP k p]
  [hp : Fact (Nat.Prime p)]
  {n : ℕ}
-- given
  (hn : (n : k) ≠ 0) :
-- imply
  (n : k) ^ (p - 1) = 1 := by
-- proof
  have h := natCast_pow_charP (k := k) p n
  have hpp : 0 < p := hp.out.pos
  have h2 : (n : k) ^ (p - 1) * (n : k) = (n : k) := by
    rw [← pow_succ]; rw [show p - 1 + 1 = p from by omega]; exact h
  calc (n : k) ^ (p - 1)
    = (n : k) ^ (p - 1) * ((n : k) * (n : k)⁻¹) := by rw [mul_inv_cancel₀ hn, mul_one]
    _ = ((n : k) ^ (p - 1) * (n : k)) * (n : k)⁻¹ := by ring
    _ = (n : k) * (n : k)⁻¹ := by rw [h2]
    _ = 1 := mul_inv_cancel₀ hn

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[cor_5_4_nonarchimedean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma cor_5_4_nonarchimedean
  [Field k]
  {v : AbsoluteValueOnField k}
  {p : ℕ}
  [CharP k p]
  [hp : Fact (Nat.Prime p)] :
-- imply
  IsNonarchimedean (v : k → ℝ) := by
-- proof
  apply thm_5_3c_backward
  intro n
  by_cases hn : (n : k) = 0
  · simp [hn, v.map_zero]
  ·
    have h := natCast_pow_char_sub_one_eq_one (k := k) p n hn
    have hv : v (n : k) ^ (p - 1) = 1 := by
      rw [← map_pow v (n : k) (p - 1), h, v.map_one]
    have hvpos : 0 < v (n : k) := by rwa [AbsoluteValue.pos_iff]
    have hp1 : p - 1 ≠ 0 := by have := hp.out.one_lt; omega
    linarith [eq_one_of_pow_eq_one_of_pos hvpos hp1 hv]
end AbsoluteValueOnField
noncomputable section
namespace AbsoluteValueOnField

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[areEquivalent_iff_isEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma areEquivalent_iff_isEquiv
  [Field k]
  {v₁ v₂ : AbsoluteValue k ℝ} :
-- imply
  AreEquivalent v₁ v₂ ↔ v₁.IsEquiv v₂ := by
-- proof
  rw [AbsoluteValue.isEquiv_iff_exists_rpow_eq]
  constructor
  · rintro ⟨α, hα, h⟩
    exact ⟨α, hα, funext fun x => (h x).symm⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun x => (congr_fun h x).symm⟩
end AbsoluteValueOnField
namespace AbsoluteValueOnField

end AbsoluteValueOnField

namespace AbsoluteValueOnField

/--
[ostrowski](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AbsoluteValues.lean)
-/
@[path]
lemma ostrowski
  [Field k]
  {v : AbsoluteValue ℚ ℝ}
-- given
  (hv : v.IsNontrivial) :
-- imply
  AreEquivalent v Rat.AbsoluteValue.real ∨ ∃ p : ℕ, ∃ (_ : Fact p.Prime), AreEquivalent v (Rat.AbsoluteValue.padic p) := by
-- proof
  have h := Rat.AbsoluteValue.equiv_real_or_padic v hv
  cases h with
  | inl hreal =>
    exact Or.inl <| (areEquivalent_iff_isEquiv v _).mpr hreal
  | inr hpadic =>
    obtain ⟨p, ⟨hp, _⟩⟩ := hpadic
    obtain ⟨hfact, hequiv⟩ := hp
    exact Or.inr ⟨p, hfact, (areEquivalent_iff_isEquiv v _).mpr hequiv⟩
end AbsoluteValueOnField
end



-- created on 2026-10-23
