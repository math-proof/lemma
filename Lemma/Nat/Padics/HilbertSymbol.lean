import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Padics.HilbertSymbol
open hilbertSymbol
open padicHilbertSymbol


namespace hilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_iff
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ↔ IsSolvable F a b := by
-- proof
  simp [hilbertSymbol]

end hilbertSymbol

namespace hilbertSymbol.padicHilbertSymbol

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_iff
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ↔ IsSolvable F a b :=
-- proof
  hilbertSymbol.eq_one_iff

end hilbertSymbol.padicHilbertSymbol

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_neg_one_iff
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = -1 ↔ ¬IsSolvable F a b := by
-- proof
  simp [hilbertSymbol]


namespace hilbertSymbol

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_or_neg_one
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
-- proof
  unfold hilbertSymbol
  split_ifs <;> simp

end hilbertSymbol

namespace padicHilbertSymbol

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_neg_one_iff
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = -1 ↔ ¬IsSolvable F a b :=
-- proof
  hilbertSymbol.eq_neg_one_iff

end padicHilbertSymbol

namespace padicHilbertSymbol

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma eq_one_or_neg_one
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 :=
-- proof
  hilbertSymbol.eq_one_or_neg_one a b

end padicHilbertSymbol

namespace padicHilbertSymbol

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma sq
  {p : ℕ} [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b ^ 2 = 1 := by
-- proof
  obtain h | h <;> simp [h] := eq_one_or_neg_one a b

end padicHilbertSymbol

namespace padicHilbertSymbol

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
lemma ne_zero
  {p : ℕ} [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b ≠ 0 := by
-- proof
  obtain h | h <;> simp [h] := eq_one_or_neg_one a b

end padicHilbertSymbol


-- created on 2026-10-20
-- updated on 2026-10-26
