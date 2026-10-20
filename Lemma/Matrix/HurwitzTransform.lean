import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.HurwitzTransform
open MetaMathlibExt


/--
[hurwitzEntry_eq_zero_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
private lemma hurwitzEntry_eq_zero_of_le_eq
  [CommRing R]
  {a b : ℕ → R}
  {i j : ℕ}
-- given
  (h : 2 * j + 2 ≤ i) :
-- imply
  hurwitzEntry a b i j = 0 := by
-- proof
  apply MetaMathlibExt.hurwitzEntry_eq_zero_of_le a b h

/--
[hurwitzEntry_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
private lemma hurwitzEntry_of_even_eq
  [CommRing R]
  {a b : ℕ → R}
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (he : i % 2 = 0) :
-- imply
  hurwitzEntry a b i j = a (j - i / 2) := by
-- proof
  apply MetaMathlibExt.hurwitzEntry_of_even a b h he

/--
[hurwitzEntry_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
private lemma hurwitzEntry_of_odd_eq
  [CommRing R]
  {a b : ℕ → R}
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (ho : i % 2 ≠ 0) :
-- imply
  hurwitzEntry a b i j = b (j - (i - 1) / 2) := by
-- proof
  apply MetaMathlibExt.hurwitzEntry_of_odd a b h ho

/--
[hurwitz_half_le_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
private lemma hurwitz_half_le_of_even_eq
  [CommRing R]
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (he : i % 2 = 0) :
-- imply
  i / 2 ≤ j := by
-- proof
  apply MetaMathlibExt.hurwitz_half_le_of_even h he

/--
[hurwitz_pred_half_le_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
private lemma hurwitz_pred_half_le_of_odd_eq
  [CommRing R]
  {i j : ℕ}
-- given
  (h : ¬2 * j + 2 ≤ i)
  (_ho : i % 2 ≠ 0) :
-- imply
  (i - 1) / 2 ≤ j := by
-- proof
  apply MetaMathlibExt.hurwitz_pred_half_le_of_odd h _ho

/--
[hurwitzTransform_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
private lemma hurwitzTransform_zero_eq
  [CommRing R]
  {a b : ℕ → R} :
-- imply
  hurwitzTransform a b 0 = a 0 := by
-- proof
  apply MetaMathlibExt.hurwitzTransform_zero a b

/--
[hurwitzTransform_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/HurwitzTransform.lean)
-/
@[path]
private lemma hurwitzTransform_one_eq
  [CommRing R]
  {a b : ℕ → R} :
-- imply
  hurwitzTransform a b 1 = a 0 * b 1 - a 1 * b 0 := by
-- proof
  apply MetaMathlibExt.hurwitzTransform_one a b


-- created on 2026-10-20
