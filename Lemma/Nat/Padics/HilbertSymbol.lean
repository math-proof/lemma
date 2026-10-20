import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.HilbertSymbol
open hilbertSymbol
open padicHilbertSymbol


/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma eq_one_iff_eq
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ↔ IsSolvable F a b := by
-- proof
  apply hilbertSymbol.eq_one_iff

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma eq_neg_one_iff_eq
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = -1 ↔ ¬IsSolvable F a b := by
-- proof
  apply hilbertSymbol.eq_neg_one_iff

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma eq_one_or_neg_one_eq
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
-- proof
  apply hilbertSymbol.eq_one_or_neg_one a b

/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma padicHilbertSymbol_eq_one_iff_eq
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ↔ IsSolvable F a b := by
-- proof
  apply padicHilbertSymbol.eq_one_iff

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma padicHilbertSymbol_eq_neg_one_iff_eq
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = -1 ↔ ¬IsSolvable F a b := by
-- proof
  apply padicHilbertSymbol.eq_neg_one_iff

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma padicHilbertSymbol_eq_one_or_neg_one_eq
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
-- proof
  apply padicHilbertSymbol.eq_one_or_neg_one a b

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma sq_eq
  {p : ℕ} [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b ^ 2 = 1 := by
-- proof
  apply padicHilbertSymbol.sq a b

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean)
-/
@[path]
private lemma ne_zero_eq
  {p : ℕ} [Fact (Nat.Prime p)]
  {a b : ℚ_[p]ˣ} :
-- imply
  padicHilbertSymbol p a b ≠ 0 := by
-- proof
  apply padicHilbertSymbol.ne_zero a b


-- created on 2026-10-20
