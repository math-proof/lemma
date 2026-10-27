import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
open hilbertSymbol padicHilbertSymbol realHilbertSymbol HilbertSymbol
open scoped Classical


namespace hilbertSymbol

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_or_neg_one
  {F : Type*}
  [Field F]
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
-- proof
  unfold hilbertSymbol; split_ifs <;> simp

end hilbertSymbol

namespace hilbertSymbol

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma sq
  {F : Type*}
  [Field F]
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b ^ 2 = 1 := by
-- proof
  obtain h | h <;> simp [h] := eq_one_or_neg_one a b

end hilbertSymbol

namespace hilbertSymbol

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma ne_zero
  {F : Type*}
  [Field F]
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b ≠ 0 := by
-- proof
  obtain h | h <;> simp [h] := eq_one_or_neg_one a b

end hilbertSymbol

namespace padicHilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_iff
  {F : Type*}
  [Field F]
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ↔ HilbertSymbol.IsSolvable F a b :=
-- proof
  hilbertSymbol.eq_one_iff

end padicHilbertSymbol

namespace padicHilbertSymbol

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_neg_one_iff
  {F : Type*}
  [Field F]
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = -1 ↔ ¬HilbertSymbol.IsSolvable F a b :=
-- proof
  hilbertSymbol.eq_neg_one_iff

end padicHilbertSymbol

namespace padicHilbertSymbol

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_or_neg_one
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = 1 ∨ padicHilbertSymbol p a b = -1 :=
-- proof
  hilbertSymbol.eq_one_or_neg_one a b

end padicHilbertSymbol

namespace padicHilbertSymbol

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma sq
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b ^ 2 = 1 :=
-- proof
  hilbertSymbol.sq a b

end padicHilbertSymbol

namespace padicHilbertSymbol

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma ne_zero
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b ≠ 0 :=
-- proof
  hilbertSymbol.ne_zero a b

end padicHilbertSymbol

namespace realHilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_iff
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = 1 ↔ ∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
-- proof
  hilbertSymbol.eq_one_iff

end realHilbertSymbol

namespace realHilbertSymbol

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_neg_one_iff
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = -1 ↔ ¬∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
-- proof
  hilbertSymbol.eq_neg_one_iff

end realHilbertSymbol

namespace realHilbertSymbol

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_or_neg_one
  {F : Type*}
  [Field F]
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = 1 ∨ realHilbertSymbol a b = -1 :=
-- proof
  hilbertSymbol.eq_one_or_neg_one a b

end realHilbertSymbol

namespace realHilbertSymbol

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma sq
  {F : Type*}
  [Field F]
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b ^ 2 = 1 :=
-- proof
  hilbertSymbol.sq a b

end realHilbertSymbol

namespace realHilbertSymbol

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma ne_zero
  {F : Type*}
  [Field F]
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b ≠ 0 :=
-- proof
  hilbertSymbol.ne_zero a b

end realHilbertSymbol

namespace realHilbertSymbol

/--
[isSolvable_of_pos_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isSolvable_of_pos_left
  {F : Type*}
  [Field F]
  {a b : ℝˣ}
-- given
  (ha : (0 : ℝ) < (a : ℝ)) :
-- imply
  HilbertSymbol.IsSolvable ℝ a b :=
-- proof
  ⟨Real.sqrt ((a : ℝ)⁻¹), 0, by
    simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
    rw [_root_.sq, ← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt ha)),
      Real.sqrt_mul_self (inv_nonneg.mpr (le_of_lt ha))]
    exact mul_inv_cancel₀ (ne_of_gt ha)⟩

end realHilbertSymbol

namespace realHilbertSymbol

/--
[isSolvable_of_pos_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isSolvable_of_pos_right
  {F : Type*}
  [Field F]
  {a b : ℝˣ}
-- given
  (hb : (0 : ℝ) < (b : ℝ)) :
-- imply
  HilbertSymbol.IsSolvable ℝ a b :=
-- proof
  ⟨0, Real.sqrt ((b : ℝ)⁻¹), by
    simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
    rw [_root_.sq, ← Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hb)),
      Real.sqrt_mul_self (inv_nonneg.mpr (le_of_lt hb))]
    exact mul_inv_cancel₀ (ne_of_gt hb)⟩

end realHilbertSymbol

namespace realHilbertSymbol

/--
[not_isSolvable_of_both_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma not_isSolvable_of_both_neg
  {F : Type*}
  [Field F]
  {a b : ℝˣ}
-- given
  (ha : (a : ℝ) < 0)
  (hb : (b : ℝ) < 0) :
-- imply
  ¬HilbertSymbol.IsSolvable ℝ a b := by
-- proof
  rintro ⟨x, y, hxy⟩
  have h1 : (a : ℝ) * x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha) (sq_nonneg x)
  have h2 : (b : ℝ) * y ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt hb) (sq_nonneg y)
  linarith

end realHilbertSymbol

namespace realHilbertSymbol

/--
[eq_neg_one_iff_both_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma eq_neg_one_iff_both_neg
  {F : Type*}
  [Field F]
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
-- proof
  rw [realHilbertSymbol, hilbertSymbol.eq_neg_one_iff]
  constructor
  · intro hns
    constructor
    · by_contra ha
      push Not at ha
      exact hns (isSolvable_of_pos_left (lt_of_le_of_ne ha (Ne.symm a.ne_zero)))
    · by_contra hb
      push Not at hb
      exact hns (isSolvable_of_pos_right (lt_of_le_of_ne hb (Ne.symm b.ne_zero)))
  · rintro ⟨ha, hb⟩
    exact not_isSolvable_of_both_neg ha hb
end realHilbertSymbol
namespace HilbertSymbol
section SolvableRepresentsZero


namespace HilbertSymbol

/--
[IsSolvable.representsZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma IsSolvable.representsZero
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ}
-- given
  (h : IsSolvable F a b) :
-- imply
  RepresentsZero F a b := by
-- proof
  obtain ⟨x₀, y₀, hxy⟩ := h
  exact ⟨x₀, y₀, 1, Or.inr (Or.inr one_ne_zero), by rw [one_pow]; exact hxy.symm⟩

end HilbertSymbol

namespace HilbertSymbol

/--
[y_ne_zero_of_binary_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma y_ne_zero_of_binary_zero
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ}
  {x₀ y₀ : F}
-- given
  (hx₀ : x₀ ≠ 0)
  (h0 : (a : F) * x₀ ^ 2 + (b : F) * y₀ ^ 2 = 0) :
-- imply
  y₀ ≠ 0 := by
-- proof
  intro hy
  rw [hy, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at h0
  obtain ha | hx := mul_eq_zero.mp h0
  · exact a.ne_zero ha
  · exact hx₀ (pow_eq_zero_iff two_ne_zero |>.mp hx)

end HilbertSymbol

namespace HilbertSymbol

/--
[binary_form_represents_all](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma binary_form_represents_all
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ}
  {x₀ y₀ : F}
  {c : F}
-- given
  (hx₀ : x₀ ≠ 0)
  (h0 : (a : F) * x₀ ^ 2 + (b : F) * y₀ ^ 2 = 0) :
-- imply
  ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = c := by
-- proof
  set α := y₀ / x₀
  have hα : α ≠ 0 := div_ne_zero (y_ne_zero_of_binary_zero hx₀ h0) hx₀
  have ha : (a : F) = -(b : F) * α ^ 2 := by
    have hx₀2 : x₀ ^ 2 ≠ 0 := pow_ne_zero 2 hx₀
    rw [div_pow,
      show -(b : F) * (y₀ ^ 2 / x₀ ^ 2) = -(b : F) * y₀ ^ 2 / x₀ ^ 2 from by ring,
      eq_div_iff hx₀2]
    linear_combination h0
  refine ⟨(c / (b : F) - 1) / (2 * α), (1 + c / (b : F)) / 2, ?_⟩
  rw [ha]; field_simp; ring

end HilbertSymbol

namespace HilbertSymbol

/--
[RepresentsZero.isSolvable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma RepresentsZero.isSolvable
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ}
-- given
  (h : RepresentsZero F a b) :
-- imply
  IsSolvable F a b := by
-- proof
  obtain ⟨x, y, z, hne, heq⟩ := h
  by_cases hz : z ≠ 0
  ·
    refine ⟨x / z, y / z, ?_⟩
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
    rw [div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
      div_eq_one_iff_eq hz2]
    exact heq.symm
  ·
    push Not at hz; subst hz
    rw [zero_pow (by norm_num : 2 ≠ 0)] at heq
    have h0 : (a : F) * x ^ 2 + (b : F) * y ^ 2 = 0 := heq.symm
    have hx : x ≠ 0 := by
      obtain hx | hy | hz' := hne
      · exact hx
      · intro hx_eq
        rw [hx_eq, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at h0
        obtain hb | hy2 := mul_eq_zero.mp h0
        · exact b.ne_zero hb
        · exact hy (pow_eq_zero_iff two_ne_zero |>.mp hy2)
      · exact absurd rfl hz'
    exact binary_form_represents_all hx h0 1

end HilbertSymbol

namespace HilbertSymbol

/--
[isSolvable_iff_representsZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isSolvable_iff_representsZero
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ} :
-- imply
  IsSolvable F a b ↔ RepresentsZero F a b :=
-- proof
  ⟨IsSolvable.representsZero, RepresentsZero.isSolvable⟩
end SolvableRepresentsZero
section RepresentsZeroNorm

end HilbertSymbol

namespace HilbertSymbol

/--
[IsNormFromSqrtExt.representsZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma IsNormFromSqrtExt.representsZero
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ}
-- given
  (h : IsNormFromSqrtExt F a b) :
-- imply
  RepresentsZero F a b := by
-- proof
  obtain ⟨z, y, hzy⟩ := h
  refine ⟨1, y, z, Or.inl one_ne_zero, ?_⟩
  rw [one_pow, mul_one]; linear_combination hzy

end HilbertSymbol

namespace HilbertSymbol

/--
[RepresentsZero.isNormFromSqrtExt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma RepresentsZero.isNormFromSqrtExt
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ}
-- given
  (h : RepresentsZero F a b) :
-- imply
  IsNormFromSqrtExt F a b := by
-- proof
  obtain ⟨x, y, z, hne, heq⟩ := h
  by_cases hx : x ≠ 0
  ·
    refine ⟨z / x, y / x, ?_⟩
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    field_simp; linear_combination heq
  ·
    push Not at hx; subst hx
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at heq
    have hy : y ≠ 0 := by
      obtain h1 | h2 | h3 := hne
      · exact absurd rfl h1
      · exact h2
      · intro hy_eq; rw [hy_eq, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at heq
        exact h3 (pow_eq_zero_iff two_ne_zero |>.mp heq)
    have hz : z ≠ 0 := by
      intro hz_eq; rw [hz_eq, zero_pow (by norm_num : 2 ≠ 0)] at heq
      obtain hb | hy2 := mul_eq_zero.mp heq.symm
      · exact b.ne_zero hb
      · exact hy (pow_eq_zero_iff two_ne_zero |>.mp hy2)
    set γ := z / y
    have hγ : γ ≠ 0 := div_ne_zero hz hy
    have hb_eq : (b : F) = γ ^ 2 := by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hy)]; exact heq.symm
    refine ⟨((a : F) + 1) / 2, ((a : F) - 1) / (2 * γ), ?_⟩
    rw [hb_eq]; field_simp; ring

end HilbertSymbol

namespace HilbertSymbol

/--
[representsZero_iff_isNormFromSqrtExt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma representsZero_iff_isNormFromSqrtExt
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b : Fˣ} :
-- imply
  RepresentsZero F a b ↔ IsNormFromSqrtExt F a b :=
-- proof
  ⟨RepresentsZero.isNormFromSqrtExt, IsNormFromSqrtExt.representsZero⟩

end HilbertSymbol

namespace HilbertSymbol

/--
[toZpDiv_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma toZpDiv_coe
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]}
-- given
  (h : ‖a‖ ≤ ‖b‖) :
-- imply
  (↑(toZpDiv h) : ℚ_[p]) = a / b :=
-- proof
  rfl

end HilbertSymbol

namespace HilbertSymbol

/--
[ne_zero_of_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma ne_zero_of_norm_le
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]}
-- given
  (ha : a ≠ 0)
  (h : ‖a‖ ≤ ‖b‖) :
-- imply
  b ≠ 0 := by
-- proof
  intro hb; rw [hb, norm_zero] at h
  exact absurd h (not_le.mpr (norm_pos_iff.mpr ha))

end HilbertSymbol

namespace HilbertSymbol

/--
[exists_max_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma exists_max_norm
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {x y z : ℚ_[p]}
-- given
  (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
-- imply
  (‖y‖ ≤ ‖x‖ ∧ ‖z‖ ≤ ‖x‖ ∧ x ≠ 0) ∨ (‖x‖ ≤ ‖y‖ ∧ ‖z‖ ≤ ‖y‖ ∧ y ≠ 0) ∨ (‖x‖ ≤ ‖z‖ ∧ ‖y‖ ≤ ‖z‖ ∧ z ≠ 0) := by
-- proof
  by_cases hxy : ‖x‖ ≤ ‖y‖
  · by_cases hyz : ‖y‖ ≤ ‖z‖
    · right; right
      exact ⟨le_trans hxy hyz, hyz,
        hne.elim (ne_zero_of_norm_le · (le_trans hxy hyz))
          (·.elim (ne_zero_of_norm_le · hyz) id)⟩
    · right; left
      push Not at hyz
      exact ⟨hxy, le_of_lt hyz,
        hne.elim (ne_zero_of_norm_le · hxy)
          (·.elim id (ne_zero_of_norm_le · (le_of_lt hyz)))⟩
  · push Not at hxy
    by_cases hxz : ‖x‖ ≤ ‖z‖
    · right; right
      exact ⟨hxz, le_trans (le_of_lt hxy) hxz,
        hne.elim (ne_zero_of_norm_le · hxz)
          (·.elim (ne_zero_of_norm_le · (le_trans (le_of_lt hxy) hxz)) id)⟩
    · left
      push Not at hxz
      exact ⟨le_of_lt hxy, le_of_lt hxz,
        hne.elim id
          (·.elim (ne_zero_of_norm_le · (le_of_lt hxy))
            (ne_zero_of_norm_le · (le_of_lt hxz)))⟩

end HilbertSymbol

namespace HilbertSymbol

/--
[primitive_of_x_max](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma primitive_of_x_max
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ}
  {x y z : ℚ_[p]}
-- given
  (hx : x ≠ 0)
  (hyx : ‖y‖ ≤ ‖x‖)
  (hzx : ‖z‖ ≤ ‖x‖)
  (heq : z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
-- imply
  HasPrimitiveSolution a b := by
-- proof
  refine ⟨1, toZpDiv hyx, toZpDiv hzx, Or.inl isUnit_one, ?_⟩
  simp only [toZpDiv_coe, PadicInt.coe_one, one_pow, mul_one, div_pow]
  rw [show (a : ℚ_[p]) + (b : ℚ_[p]) * (y ^ 2 / x ^ 2) =
    ((a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) / x ^ 2 from by field_simp, heq]

end HilbertSymbol

namespace HilbertSymbol

/--
[primitive_of_y_max](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma primitive_of_y_max
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ}
  {x y z : ℚ_[p]}
-- given
  (hy : y ≠ 0)
  (hxy : ‖x‖ ≤ ‖y‖)
  (hzy : ‖z‖ ≤ ‖y‖)
  (heq : z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
-- imply
  HasPrimitiveSolution a b := by
-- proof
  refine ⟨toZpDiv hxy, 1, toZpDiv hzy, Or.inr (Or.inl isUnit_one), ?_⟩
  simp only [toZpDiv_coe, PadicInt.coe_one, one_pow, mul_one, div_pow]
  rw [show (a : ℚ_[p]) * (x ^ 2 / y ^ 2) + (b : ℚ_[p]) =
    ((a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) / y ^ 2 from by field_simp, heq]

end HilbertSymbol

namespace HilbertSymbol

/--
[primitive_of_z_max](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma primitive_of_z_max
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ}
  {x y z : ℚ_[p]}
-- given
  (hz : z ≠ 0)
  (hxz : ‖x‖ ≤ ‖z‖)
  (hyz : ‖y‖ ≤ ‖z‖)
  (heq : z ^ 2 = (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) :
-- imply
  HasPrimitiveSolution a b := by
-- proof
  refine ⟨toZpDiv hxz, toZpDiv hyz, 1, Or.inr (Or.inr isUnit_one), ?_⟩
  simp only [toZpDiv_coe, PadicInt.coe_one, one_pow, div_pow]
  rw [show (a : ℚ_[p]) * (x ^ 2 / z ^ 2) + (b : ℚ_[p]) * (y ^ 2 / z ^ 2) =
    ((a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2) / z ^ 2 from by field_simp,
    ← heq, div_self (pow_ne_zero 2 hz)]

end HilbertSymbol

namespace HilbertSymbol

/--
[RepresentsZero.hasPrimitiveSolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma RepresentsZero.hasPrimitiveSolution
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ}
-- given
  (h : RepresentsZero ℚ_[p] a b) :
-- imply
  HasPrimitiveSolution a b := by
-- proof
  obtain ⟨x, y, z, hne, heq⟩ := h
  obtain ⟨hyx, hzx, hx⟩ | ⟨hxy, hzy, hy⟩ | ⟨hxz, hyz, hz⟩ := exists_max_norm hne
  · exact primitive_of_x_max hx hyx hzx heq
  · exact primitive_of_y_max hy hxy hzy heq
  · exact primitive_of_z_max hz hxz hyz heq

end HilbertSymbol

namespace HilbertSymbol

/--
[HasPrimitiveSolution.representsZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma HasPrimitiveSolution.representsZero
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ}
-- given
  (h : HasPrimitiveSolution a b) :
-- imply
  RepresentsZero ℚ_[p] a b := by
-- proof
  obtain ⟨x, y, z, hunit, heq⟩ := h
  refine ⟨↑x, ↑y, ↑z, ?_, heq.symm⟩
  obtain hu | hu | hu := hunit
  · left; exact PadicInt.coe_ne_zero.mpr hu.ne_zero
  · right; left; exact PadicInt.coe_ne_zero.mpr hu.ne_zero
  · right; right; exact PadicInt.coe_ne_zero.mpr hu.ne_zero

end HilbertSymbol

namespace HilbertSymbol

/--
[representsZero_iff_hasPrimitiveSolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma representsZero_iff_hasPrimitiveSolution
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  RepresentsZero ℚ_[p] a b ↔ HasPrimitiveSolution a b :=
-- proof
  ⟨RepresentsZero.hasPrimitiveSolution, HasPrimitiveSolution.representsZero⟩

end HilbertSymbol

namespace HilbertSymbol

/--
[lemma_10_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma lemma_10_2
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  IsSolvable ℚ_[p] a b ↔ RepresentsZero ℚ_[p] a b :=
-- proof
  isSolvable_iff_representsZero

end HilbertSymbol

namespace HilbertSymbol

/--
[isSolvable_iff_hasPrimitiveSolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isSolvable_iff_hasPrimitiveSolution
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  IsSolvable ℚ_[p] a b ↔ HasPrimitiveSolution a b := by
-- proof
  rw [isSolvable_iff_representsZero, representsZero_iff_hasPrimitiveSolution]

end HilbertSymbol

namespace HilbertSymbol

/--
[isSolvable_iff_isNormFromSqrtExt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isSolvable_iff_isNormFromSqrtExt
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  IsSolvable ℚ_[p] a b ↔ IsNormFromSqrtExt ℚ_[p] a b := by
-- proof
  rw [isSolvable_iff_representsZero, representsZero_iff_isNormFromSqrtExt]

end HilbertSymbol

namespace HilbertSymbol

/--
[hasPrimitiveSolution_iff_isNormFromSqrtExt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hasPrimitiveSolution_iff_isNormFromSqrtExt
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  HasPrimitiveSolution a b ↔ IsNormFromSqrtExt ℚ_[p] a b := by
-- proof
  rw [← representsZero_iff_hasPrimitiveSolution, representsZero_iff_isNormFromSqrtExt]

end HilbertSymbol

namespace HilbertSymbol

/--
[hilbert_eq_one_iff_representsZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hilbert_eq_one_iff_representsZero
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = 1 ↔ RepresentsZero ℚ_[p] a b := by
-- proof
  rw [padicHilbertSymbol.eq_one_iff]; exact isSolvable_iff_representsZero

end HilbertSymbol

namespace HilbertSymbol

/--
[hilbert_eq_one_iff_hasPrimitiveSolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hilbert_eq_one_iff_hasPrimitiveSolution
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = 1 ↔ HasPrimitiveSolution a b := by
-- proof
  rw [padicHilbertSymbol.eq_one_iff]; exact isSolvable_iff_hasPrimitiveSolution a b

end HilbertSymbol

namespace HilbertSymbol

/--
[hilbert_eq_one_iff_isNormFromSqrtExt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hilbert_eq_one_iff_isNormFromSqrtExt
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = 1 ↔ IsNormFromSqrtExt ℚ_[p] a b := by
-- proof
  rw [padicHilbertSymbol.eq_one_iff]; exact isSolvable_iff_isNormFromSqrtExt a b
end HilbertSymbol
namespace hilbertSymbol
variable {F : Type*} [Field F]
section Cor103


namespace hilbertSymbol

/--
[hilbert_neg_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hilbert_neg_self
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {c : Fˣ} :
-- imply
  hilbertSymbol F (-c) c = 1 := by
-- proof
  rw [eq_one_iff]
  refine ⟨((c : F)⁻¹ - 1) / 2, (1 + (c : F)⁻¹) / 2, ?_⟩
  have hc : (c : F) ≠ 0 := c.ne_zero
  simp only [Units.val_neg]
  field_simp
  ring

end hilbertSymbol

namespace hilbertSymbol

/--
[isNormFromSqrtExt_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isNormFromSqrtExt_mul
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b c : Fˣ}
-- given
  (ha : HilbertSymbol.IsNormFromSqrtExt F a c)
  (hb : HilbertSymbol.IsNormFromSqrtExt F b c) :
-- imply
  HilbertSymbol.IsNormFromSqrtExt F (a * b) c := by
-- proof
  obtain ⟨z₀, w₀, h₀⟩ := ha
  obtain ⟨z₁, w₁, h₁⟩ := hb
  refine ⟨z₀ * z₁ + (c : F) * w₀ * w₁, z₀ * w₁ + z₁ * w₀, ?_⟩
  simp only [Units.val_mul]
  linear_combination (z₁ ^ 2 - ↑c * w₁ ^ 2) * h₀ + (↑a : F) * h₁

end hilbertSymbol

namespace hilbertSymbol

/--
[isSolvable_mul_of_isSolvable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isSolvable_mul_of_isSolvable
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b c : Fˣ}
-- given
  (ha : HilbertSymbol.IsSolvable F a c)
  (hb : HilbertSymbol.IsSolvable F b c) :
-- imply
  HilbertSymbol.IsSolvable F (a * b) c := by
-- proof
  rw [HilbertSymbol.isSolvable_iff_representsZero,
    HilbertSymbol.representsZero_iff_isNormFromSqrtExt]
  exact isNormFromSqrtExt_mul
    ((HilbertSymbol.isSolvable_iff_representsZero.mp ha |>
      HilbertSymbol.representsZero_iff_isNormFromSqrtExt.mp))
    ((HilbertSymbol.isSolvable_iff_representsZero.mp hb |>
      HilbertSymbol.representsZero_iff_isNormFromSqrtExt.mp))

end hilbertSymbol

namespace hilbertSymbol

/--
[isSolvable_inv_of_isSolvable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma isSolvable_inv_of_isSolvable
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a c : Fˣ}
-- given
  (h : HilbertSymbol.IsSolvable F a c) :
-- imply
  HilbertSymbol.IsSolvable F a⁻¹ c := by
-- proof
  obtain ⟨x₀, y₀, hxy⟩ := h
  refine ⟨(a : F) * x₀, y₀, ?_⟩
  simp only [Units.val_inv_eq_inv_val, mul_pow]
  have : (↑a : F)⁻¹ * ((↑a : F) ^ 2 * x₀ ^ 2) = ↑a * x₀ ^ 2 := by field_simp
  rw [this]; exact hxy

end hilbertSymbol

namespace hilbertSymbol

/--
[hilbert_mul_of_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hilbert_mul_of_eq_one
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {a b c : Fˣ}
-- given
  (h : hilbertSymbol F a c = 1) :
-- imply
  hilbertSymbol F a c * hilbertSymbol F b c = hilbertSymbol F (a * b) c := by
-- proof
  rw [h, one_mul]
  have ha : HilbertSymbol.IsSolvable F a c := eq_one_iff.mp h
  obtain hb | hb <;> := eq_one_or_neg_one b c
    obtain hab | hab := eq_one_or_neg_one (a * b) c
  · rw [hb, hab]
  · exfalso
    exact eq_neg_one_iff.mp hab (isSolvable_mul_of_isSolvable ha (eq_one_iff.mp hb))
  · exfalso
    have habs := eq_one_iff.mp hab
    have hbs := isSolvable_mul_of_isSolvable (isSolvable_inv_of_isSolvable ha) habs
    rw [show (a⁻¹ * (a * b) : Fˣ) = b from by simp] at hbs
    exact eq_neg_one_iff.mp hb hbs
  · rw [hb, hab]

end hilbertSymbol

namespace hilbertSymbol

/--
[hilbert_self_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hilbert_self_eq_neg_one
  {F : Type*}
  [Field F]
  [Field F]
  [CharZero F]
  {c : Fˣ} :
-- imply
  hilbertSymbol F c c = hilbertSymbol F (-1) c := by
-- proof
  have h_neg_c : hilbertSymbol F (-c) c = 1 := hilbert_neg_self c
  have key := hilbert_mul_of_eq_one (-c) (-1) c h_neg_c
  simp only [h_neg_c, one_mul] at key
  rwa [show ((-c) * (-1) : Fˣ) = c from by ext; simp] at key
end Cor103
end hilbertSymbol


namespace HilbertSymbol

/--
[unitZpToQp_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma unitZpToQp_coe
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {u : ℤ_[p]ˣ} :
-- imply
  (unitZpToQp u : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) := by
-- proof
  simp [unitZpToQp, Units.coe_map]
set_option maxHeartbeats 800000 in

end HilbertSymbol

namespace HilbertSymbol

/--
[chevalley_warning_hensel_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma chevalley_warning_hensel_lift
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact p.Prime]
  {u v : ℤ_[p]ˣ}
-- given
  (hp_odd : p ≠ 2) :
-- imply
  ∃ (x₀ y₀ : ℤ_[p]) (z₀ : ℤ_[p]ˣ), (z₀ : ℤ_[p]) ^ 2 = (u : ℤ_[p]) * x₀ ^ 2 + (v : ℤ_[p]) * y₀ ^ 2 := by
-- proof
  have hp := Fact.out (p := Nat.Prime p)
  have hu_unit : IsUnit (PadicInt.toZMod (u : ℤ_[p])) :=
    RingHom.isUnit_map PadicInt.toZMod u.isUnit
  have hv_unit : IsUnit (PadicInt.toZMod (v : ℤ_[p])) :=
    RingHom.isUnit_map PadicInt.toZMod v.isUnit
  set u_bar := hu_unit.unit
  set v_bar := hv_unit.unit
  have hu_bar_val : (u_bar : ZMod p) = PadicInt.toZMod (u : ℤ_[p]) := by
    simp [u_bar, IsUnit.unit_spec]
  have hv_bar_val : (v_bar : ZMod p) = PadicInt.toZMod (v : ℤ_[p]) := by
    simp [v_bar, IsUnit.unit_spec]
  open Polynomial in
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card p]
    exact Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two hp hp_odd)
  have hu_ne : (u_bar : ZMod p) ≠ 0 := Units.ne_zero _
  have hv_ne : (v_bar : ZMod p) ≠ 0 := Units.ne_zero _
  open Polynomial in
  have hf : (C (u_bar : ZMod p) * X ^ 2 - C 1).degree = 2 := by
    rw [degree_sub_eq_left_of_degree_lt]
    · simp [degree_C_mul_X_pow 2 hu_ne]
    · rw [degree_C_mul_X_pow 2 hu_ne]; simp
  open Polynomial in
  have hg : (C (v_bar : ZMod p) * X ^ 2).degree = 2 := by
    simp [degree_C_mul_X_pow 2 hv_ne]
  open Polynomial in
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  open Polynomial in
  have hab' : (u_bar : ZMod p) * a ^ 2 + (v_bar : ZMod p) * b ^ 2 = 1 := by
    have : (u_bar : ZMod p) * a ^ 2 - 1 + (v_bar : ZMod p) * b ^ 2 = 0 := by
      convert hab using 1
      simp [eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination this
  obtain ⟨a_lift, ha_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod a
  obtain ⟨b_lift, hb_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod b
  set c := (u : ℤ_[p]) * a_lift ^ 2 + (v : ℤ_[p]) * b_lift ^ 2 with hc_def
  have hc_mod : PadicInt.toZMod c = 1 := by
    simp only [hc_def, map_add, map_mul, map_pow, ha_lift, hb_lift,
      ← hu_bar_val, ← hv_bar_val]
    exact hab'
  have hnorm_1_sub_c : ‖(1 : ℤ_[p]) - c‖ < 1 := by
    have hmem : (1 - c) ∈ RingHom.ker PadicInt.toZMod :=
      show PadicInt.toZMod (1 - c) = 0 by simp [map_sub, map_one, hc_mod]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hmem
    exact (PadicInt.norm_lt_one_iff_dvd _).2 hmem
  have hnorm_two : ‖(2 : ℤ_[p])‖ = 1 := by
    have h1 : ‖(2 : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
    have h2 : ¬ (‖(2 : ℤ_[p])‖ < 1) := by
      rw [show (2 : ℤ_[p]) = ((2 : ℤ) : ℤ_[p]) from by push_cast; ring]
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      intro hdvd
      have h3 : p ∣ 2 := by exact_mod_cast hdvd
      have h4 := Nat.le_of_dvd (by norm_num) h3
      have h5 := hp.two_le
      omega
    linarith
  open Polynomial in
  have h_aeval : Polynomial.aeval (1 : ℤ_[p]) (X ^ 2 - C c : Polynomial ℤ_[p]) = 1 - c := by
    simp [aeval_def]
  open Polynomial in
  have h_deriv : Polynomial.aeval (1 : ℤ_[p])
    (Polynomial.derivative (X ^ 2 - C c : Polynomial ℤ_[p])) = 2 := by
    simp [derivative_sub, derivative_pow, derivative_C, derivative_X, aeval_def]
  open Polynomial in
  have hensel_hyp : ‖Polynomial.aeval (1 : ℤ_[p]) (X ^ 2 - C c : Polynomial ℤ_[p])‖ <
    ‖Polynomial.aeval (1 : ℤ_[p])
      (Polynomial.derivative (X ^ 2 - C c : Polynomial ℤ_[p]))‖ ^ 2 := by
    rwa [h_aeval, h_deriv, hnorm_two, one_pow]
  open Polynomial in
  obtain ⟨z₀, hz₀_eval, hz₀_close, _, _⟩ := hensels_lemma hensel_hyp
  open Polynomial in
  have hz₀_sq : z₀ ^ 2 = c := by
    simp [aeval_def] at hz₀_eval
    linear_combination hz₀_eval
  open Polynomial in
  have hz₀_close' : ‖z₀ - 1‖ < 1 := by
    have : ‖z₀ - 1‖ < ‖Polynomial.aeval (1 : ℤ_[p])
      (Polynomial.derivative (X ^ 2 - C c : Polynomial ℤ_[p]))‖ := hz₀_close
    rwa [h_deriv, hnorm_two] at this
  have hz₀_unit : IsUnit z₀ := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖(1 : ℤ_[p])‖ = 1 := by simp
    have hne : ‖z₀ - 1‖ ≠ ‖(1 : ℤ_[p])‖ := by
      rw [h1]; exact ne_of_lt hz₀_close'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    rw [sub_add_cancel] at this
    rw [this, h1, max_eq_right (le_of_lt hz₀_close')]
  refine ⟨a_lift, b_lift, hz₀_unit.unit, ?_⟩
  rw [IsUnit.unit_spec, hz₀_sq]

end HilbertSymbol

namespace HilbertSymbol

/--
[hilbert_symbol_units_eq_one_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
lemma hilbert_symbol_units_eq_one_of_odd
  {F : Type*}
  [Field F]
  {p : ℕ}
  [Fact p.Prime]
  {u v : ℤ_[p]ˣ}
-- given
  (hp_odd : p ≠ 2) :
-- imply
  padicHilbertSymbol p (unitZpToQp u) (unitZpToQp v) = 1 := by
-- proof
  rw [padicHilbertSymbol.eq_one_iff]
  obtain ⟨x₀, y₀, z₀, hz⟩ := chevalley_warning_hensel_lift p hp_odd u v
  have hz_qp : ((z₀ : ℤ_[p]) : ℚ_[p]) ^ 2 =
    ((u : ℤ_[p]) : ℚ_[p]) * ((x₀ : ℚ_[p])) ^ 2 +
    ((v : ℤ_[p]) : ℚ_[p]) * ((y₀ : ℚ_[p])) ^ 2 := by
    have := congrArg (PadicInt.Coe.ringHom (p := p)) hz
    simp only [map_pow, map_mul, map_add] at this
    exact this
  have hz_ne : ((z₀ : ℤ_[p]) : ℚ_[p]) ≠ 0 := by simp [z₀.ne_zero]
  refine ⟨↑x₀ / ↑(z₀ : ℤ_[p]), ↑y₀ / ↑(z₀ : ℤ_[p]), ?_⟩
  rw [unitZpToQp_coe, unitZpToQp_coe,
    div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
    div_eq_one_iff_eq (pow_ne_zero 2 hz_ne)]
  exact hz_qp.symm

end HilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
private lemma eq_one_iff_eq_3
  {F : Type*}
  [Field F]
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = 1 ↔ ∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 := by
-- proof
  apply realHilbertSymbol.eq_one_iff F

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean)
-/
@[path]
private lemma eq_neg_one_iff_eq_3
  {F : Type*}
  [Field F]
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = -1 ↔ ¬∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 := by
-- proof
  apply realHilbertSymbol.eq_neg_one_iff F


-- created on 2026-10-23
