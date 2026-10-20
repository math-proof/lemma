import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MotzkinTriangle
open MetaMathlibExt
open MotzkinRiordanPair


/--
[motzkinSquareRoot_isSquareRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinSquareRoot_isSquareRoot_eq
  :
-- imply
  IsMotzkinSquareRoot motzkinSquareRoot := by
-- proof
  apply MetaMathlibExt.motzkinSquareRoot_isSquareRoot

/--
[two_mul_X_mul_motzkinH](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma two_mul_X_mul_motzkinH_eq
  :
-- imply
  2 * PowerSeries.X * motzkinH = 1 - PowerSeries.X - motzkinSquareRoot := by
-- proof
  apply MetaMathlibExt.two_mul_X_mul_motzkinH

/--
[motzkinG_mul_motzkinSquareRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinG_mul_motzkinSquareRoot_eq
  :
-- imply
  motzkinG * motzkinSquareRoot = 1 := by
-- proof
  apply MetaMathlibExt.motzkinG_mul_motzkinSquareRoot

/--
[entry_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma entry_zero_right_eq
  {p : MotzkinRiordanPair}
  {n : ℕ} :
-- imply
  p.entry n 0 = p.g.coeff n := by
-- proof
  apply MetaMathlibExt.MotzkinRiordanPair.entry_zero_right p n

/--
[motzkinTriangle_initial_rows](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinTriangle_initial_rows_eq
  :
-- imply
  [[motzkinTriangle 0 0],
    [motzkinTriangle 1 0, motzkinTriangle 1 1],
    [motzkinTriangle 2 0, motzkinTriangle 2 1, motzkinTriangle 2 2],
    [motzkinTriangle 3 0, motzkinTriangle 3 1,
    motzkinTriangle 3 2, motzkinTriangle 3 3]] =
    [[1], [1, 1], [3, 2, 1], [7, 6, 3, 1]] := by
-- proof
  apply MetaMathlibExt.motzkinTriangle_initial_rows


-- created on 2026-10-20
