import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Padics.HilbertSymbol


namespace hilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_iff
  {F : Type*}
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ↔ HilbertSymbol.IsSolvable F a b := by
-- proof
  simp [hilbertSymbol]

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_neg_one_iff
  {F : Type*}
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = -1 ↔ ¬ HilbertSymbol.IsSolvable F a b := by
-- proof
  simp [hilbertSymbol]

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_or_neg_one
  {F : Type*}
  [Field F]
-- given
  (a b : Fˣ) :
-- imply
  hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
-- proof
  unfold hilbertSymbol
  split_ifs <;> simp

end hilbertSymbol

namespace padicHilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_iff
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = 1 ↔
    ∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
-- proof
  hilbertSymbol.eq_one_iff

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_neg_one_iff
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b = -1 ↔
    ¬ ∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
-- proof
  hilbertSymbol.eq_neg_one_iff

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_or_neg_one
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (a b : ℚ_[p]ˣ) :
-- imply
  padicHilbertSymbol p a b = 1 ∨ padicHilbertSymbol p a b = -1 :=
-- proof
  hilbertSymbol.eq_one_or_neg_one a b

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma sq
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (a b : ℚ_[p]ˣ) :
-- imply
  padicHilbertSymbol p a b ^ 2 = 1 := by
-- proof
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma ne_zero
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (a b : ℚ_[p]ˣ) :
-- imply
  padicHilbertSymbol p a b ≠ 0 := by
-- proof
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

end padicHilbertSymbol


-- created on 2026-10-20
-- updated on 2026-10-28
