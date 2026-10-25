import Mathlib
import sympy.Basic
import Def.NumberTheory.Padics.HilbertSymbol.Real
open realHilbertSymbol


namespace realHilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
lemma eq_one_iff
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = 1 ↔
    ∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 :=
-- proof
  hilbertSymbol.eq_one_iff

end realHilbertSymbol

namespace realHilbertSymbol

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
lemma eq_neg_one_iff
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = -1 ↔
    ¬∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 :=
-- proof
  hilbertSymbol.eq_neg_one_iff

end realHilbertSymbol

namespace realHilbertSymbol

/--
[eq_neg_one_iff_both_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
lemma eq_neg_one_iff_both_neg
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
-- proof
  have key : ∀ {c d : ℝˣ}, 0 < (c : ℝ) →
    ∃ x y : ℝ, (c : ℝ) * x ^ 2 + (d : ℝ) * y ^ 2 = 1 := by
    intro c d hc
    have hcne : (c : ℝ) ≠ 0 := Units.ne_zero c
    have hsq : (Real.sqrt (c : ℝ)) ^ 2 = (c : ℝ) := Real.sq_sqrt hc.le
    have hinv : ((Real.sqrt (c : ℝ))⁻¹) ^ 2 = (c : ℝ)⁻¹ := by
      rw [inv_pow, hsq]
    refine ⟨(Real.sqrt (c : ℝ))⁻¹, 0, ?_⟩
    rw [hinv, mul_inv_cancel₀ hcne]
    simp
  rw [eq_neg_one_iff]
  constructor
  · intro hnot
    by_cases ha : (a : ℝ) < 0
    · by_cases hb : (b : ℝ) < 0
      · exact ⟨ha, hb⟩
      · have hbpos : 0 < (b : ℝ) :=
        lt_of_le_of_ne (not_lt.mp hb) (Ne.symm (Units.ne_zero b))
        obtain ⟨x, y, hxy⟩ := key (c := b) (d := a) hbpos
        exact absurd ⟨y, x, by linear_combination hxy⟩ hnot
    · have hapos : 0 < (a : ℝ) :=
      lt_of_le_of_ne (not_lt.mp ha) (Ne.symm (Units.ne_zero a))
      obtain ⟨x, y, hxy⟩ := key (c := a) (d := b) hapos
      exact absurd ⟨x, y, hxy⟩ hnot
  · rintro ⟨ha, hb⟩ hsol
    obtain ⟨x, y, hxy⟩ := hsol
    have hx : (a : ℝ) * x ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg x)
    have hy : (b : ℝ) * y ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg y)
    linarith

end realHilbertSymbol

namespace realHilbertSymbol

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
lemma eq_one_or_neg_one
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = 1 ∨ realHilbertSymbol a b = -1 :=
-- proof
  hilbertSymbol.eq_one_or_neg_one a b

end realHilbertSymbol

namespace realHilbertSymbol

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
lemma sq
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b ^ 2 = 1 := by
-- proof
  obtain h | h <;> simp [h] := eq_one_or_neg_one a b

end realHilbertSymbol

namespace realHilbertSymbol

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
lemma ne_zero
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b ≠ 0 := by
-- proof
  obtain h | h <;> simp [h] := eq_one_or_neg_one a b

end realHilbertSymbol


-- created on 2026-10-20
-- updated on 2026-10-23
