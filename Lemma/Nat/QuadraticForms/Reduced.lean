import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.Reduced
open BinaryQuadraticForm


/--
[IsGaussReduced_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_iff_eq
  {a b c : ℤ} :
-- imply
  IsGaussReduced a b c ↔
      0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
        ((|b| = a ∨ a = c) → 0 ≤ b) := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced_iff a b c

/--
[IsGaussReduced.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_mk_eq
  {a b c : ℤ}
-- given
  (hpos : 0 < a)
  (hdisc : discrim a b c < 0)
  (habs : |b| ≤ a)
  (hac : a ≤ c)
  (hbnd : (|b| = a ∨ a = c) → 0 ≤ b) :
-- imply
  IsGaussReduced a b c := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.mk hpos hdisc habs hac hbnd

/--
[IsGaussReduced.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_pos_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  0 < a := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.pos h

/--
[IsGaussReduced.discrim_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_discrim_neg_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  discrim a b c < 0 := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.discrim_neg h

/--
[IsGaussReduced.abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_abs_le_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  |b| ≤ a := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.abs_le h

/--
[IsGaussReduced.le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_le_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  a ≤ c := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.le h

/--
[IsGaussReduced.boundary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_boundary_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  (|b| = a ∨ a = c) → 0 ≤ b := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.boundary h

/--
[IsGaussReduced.neg_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_neg_le_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  -a ≤ b := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.neg_le h

/--
[IsGaussReduced.le_of_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_le_of_abs_le_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  b ≤ a := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.le_of_abs_le h

/--
[IsGaussReduced.loose_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
private lemma IsGaussReduced_loose_bounds_eq
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  -a ≤ b ∧ b ≤ a := by
-- proof
  apply BinaryQuadraticForm.IsGaussReduced.loose_bounds h


-- created on 2026-10-20
