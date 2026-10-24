import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.HurwitzTransform
open MetaMathlibExt


namespace MetaMathlibExt

/--
[hurwitzEntry_eq_zero_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
lemma hurwitzEntry_eq_zero_of_le
  [CommRing R]
  {a b : ℕ → R}
  {i j : ℕ}
-- given
  (h : 2 * j + 2 ≤ i) :
-- imply
  hurwitzEntry a b i j = 0 := by
-- proof
  simp [hurwitzEntry, h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hurwitzEntry_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
lemma hurwitzEntry_of_even
  [CommRing R]
  {a b : ℕ → R}
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (he : i % 2 = 0) :
-- imply
  hurwitzEntry a b i j = a (j - i / 2) := by
-- proof
  simp [hurwitzEntry, h, he]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hurwitzEntry_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
lemma hurwitzEntry_of_odd
  [CommRing R]
  {a b : ℕ → R}
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (ho : i % 2 ≠ 0) :
-- imply
  hurwitzEntry a b i j = b (j - (i - 1) / 2) := by
-- proof
  simp [hurwitzEntry, h, ho]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hurwitz_half_le_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
lemma hurwitz_half_le_of_even
  [CommRing R]
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (he : i % 2 = 0) :
-- imply
  i / 2 ≤ j := by
-- proof
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hurwitz_pred_half_le_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
lemma hurwitz_pred_half_le_of_odd
  [CommRing R]
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (ho : i % 2 ≠ 0) :
-- imply
  (i - 1) / 2 ≤ j := by
-- proof
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hurwitzTransform_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
lemma hurwitzTransform_zero
  [CommRing R]
  {a b : ℕ → R} :
-- imply
  hurwitzTransform a b 0 = a 0 := by
-- proof
  unfold hurwitzTransform hurwitzMatrix
  rw [Matrix.det_fin_one]
  simp [Matrix.of_apply, hurwitzEntry]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hurwitzTransform_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
lemma hurwitzTransform_one
  [CommRing R]
  {a b : ℕ → R} :
-- imply
  hurwitzTransform a b 1 = a 0 * b 1 - a 1 * b 0 := by
-- proof
  unfold hurwitzTransform hurwitzMatrix
  rw [Matrix.det_fin_two]
  simp [Matrix.of_apply, hurwitzEntry]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
