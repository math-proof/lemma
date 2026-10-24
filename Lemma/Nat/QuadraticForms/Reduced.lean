import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.Reduced
open BinaryQuadraticForm


namespace BinaryQuadraticForm

/--
[IsGaussReduced_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced_iff
  {a b c : ℤ} :
-- imply
  IsGaussReduced a b c ↔
      0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
        ((|b| = a ∨ a = c) → 0 ≤ b) :=
-- proof
  Iff.rfl

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.mk
  {a b c : ℤ}
-- given
  (hpos : 0 < a)
  (hdisc : discrim a b c < 0)
  (habs : |b| ≤ a)
  (hac : a ≤ c)
  (hbnd : (|b| = a ∨ a = c) → 0 ≤ b) :
-- imply
  IsGaussReduced a b c :=
-- proof
  ⟨hpos, hdisc, habs, hac, hbnd⟩

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.pos
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  0 < a :=
-- proof
  h.1

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.discrim_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.discrim_neg
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  discrim a b c < 0 :=
-- proof
  h.2.1

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.abs_le
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  |b| ≤ a :=
-- proof
  h.2.2.1

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.le
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  a ≤ c :=
-- proof
  h.2.2.2.1

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.boundary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.boundary
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  (|b| = a ∨ a = c) → 0 ≤ b :=
-- proof
  h.2.2.2.2

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.neg_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.neg_le
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  -a ≤ b :=
-- proof
  (_root_.abs_le.mp h.abs_le).1

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.le_of_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.le_of_abs_le
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  b ≤ a :=
-- proof
  (_root_.abs_le.mp h.abs_le).2

end BinaryQuadraticForm

namespace BinaryQuadraticForm

/--
[IsGaussReduced.loose_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/Reduced.lean)
-/
@[path]
lemma IsGaussReduced.loose_bounds
  {a b c : ℤ}
-- given
  (h : IsGaussReduced a b c) :
-- imply
  -a ≤ b ∧ b ≤ a :=
-- proof
  _root_.abs_le.mp h.abs_le

end BinaryQuadraticForm


-- created on 2026-10-20
-- updated on 2026-10-23
