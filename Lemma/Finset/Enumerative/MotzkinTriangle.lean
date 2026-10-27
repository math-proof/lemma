import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.MotzkinTriangle.Part5
open MetaMathlibExt
open MotzkinRiordanPair


namespace MetaMathlibExt.MotzkinRiordanPair

/--
[entry_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
lemma entry_zero_right
  {p : MotzkinRiordanPair}
  {n : ℕ} :
-- imply
  p.entry n 0 = p.g.coeff n := by
-- proof
  simp [entry]

end MetaMathlibExt.MotzkinRiordanPair

namespace MetaMathlibExt

/--
[motzkinSquareRoot_coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinSquareRoot_coeff_one :
  PowerSeries.coeff 1 motzkinSquareRoot = -1 := by
  have hs := congrArg (PowerSeries.coeff 1) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_one_mul, motzkinDiscriminant,
    PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2] at hs ⊢
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinSquareRoot_coeff_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinSquareRoot_coeff_two :
  PowerSeries.coeff 2 motzkinSquareRoot = -2 := by
  have hs := congrArg (PowerSeries.coeff 2) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one] at hs ⊢
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinSquareRoot_coeff_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinSquareRoot_coeff_three :
  PowerSeries.coeff 3 motzkinSquareRoot = -2 := by
  have hs := congrArg (PowerSeries.coeff 3) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two] at hs ⊢
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinSquareRoot_coeff_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinSquareRoot_coeff_four :
  PowerSeries.coeff 4 motzkinSquareRoot = -4 := by
  have hs := congrArg (PowerSeries.coeff 4) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two,
    motzkinSquareRoot_coeff_three] at hs ⊢
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinG_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinG_coeff_zero : PowerSeries.coeff 0 motzkinG = 1 := by
  simp [motzkinG, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    motzkinSquareRoot_isSquareRoot.2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinG_coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinG_coeff_one : PowerSeries.coeff 1 motzkinG = 1 := by
  have hg := congrArg (PowerSeries.coeff 1) motzkinG_mul_motzkinSquareRoot
  rw [PowerSeries.coeff_one_mul] at hg
  have hg0 : PowerSeries.constantCoeff motzkinG = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using motzkinG_coeff_zero
  norm_num [motzkinG_coeff_zero,
    hg0, motzkinSquareRoot_isSquareRoot.2, motzkinSquareRoot_coeff_one] at hg ⊢
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinG_coeff_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinG_coeff_two : PowerSeries.coeff 2 motzkinG = 3 := by
  have hg := congrArg (PowerSeries.coeff 2) motzkinG_mul_motzkinSquareRoot
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two] at hg ⊢
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinG_coeff_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinG_coeff_three : PowerSeries.coeff 3 motzkinG = 7 := by
  have hg := congrArg (PowerSeries.coeff 3) motzkinG_mul_motzkinSquareRoot
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinG_coeff_two, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two,
    motzkinSquareRoot_coeff_three] at hg ⊢
  linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinH_coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinH_coeff_zero : PowerSeries.coeff 0 motzkinH = 0 := by
  norm_num [motzkinH, motzkinSquareRoot_coeff_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinH_coeff_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinH_coeff_one : PowerSeries.coeff 1 motzkinH = 1 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_two]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinH_coeff_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinH_coeff_two : PowerSeries.coeff 2 motzkinH = 1 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_three]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinH_coeff_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
private lemma motzkinH_coeff_three : PowerSeries.coeff 3 motzkinH = 2 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_four]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[motzkinTriangle_initial_rows](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinTriangle.lean)
-/
@[path]
lemma motzkinTriangle_initial_rows
  :
-- imply
  [[motzkinTriangle 0 0],
    [motzkinTriangle 1 0, motzkinTriangle 1 1],
    [motzkinTriangle 2 0, motzkinTriangle 2 1, motzkinTriangle 2 2],
    [motzkinTriangle 3 0, motzkinTriangle 3 1,
    motzkinTriangle 3 2, motzkinTriangle 3 3]] =
    [[1], [1, 1], [3, 2, 1], [7, 6, 3, 1]] := by
-- proof
  norm_num [motzkinTriangle, motzkinRiordanPair, MotzkinRiordanPair.entry,
    pow_succ, PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinG_coeff_two, motzkinG_coeff_three,
    motzkinH_coeff_zero, motzkinH_coeff_one, motzkinH_coeff_two,
    motzkinH_coeff_three]

end MetaMathlibExt

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


-- created on 2026-10-20
-- updated on 2026-10-26
