import Mathlib
import sympy.Basic
import Theorem.NumberTheory.PolygonalNumber
open Nat


namespace Nat

/--
[two_choose_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma two_choose_add (n : ℕ) : 2 * (Nat.choose n 2) + n = n ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpascal : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
      simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ n 1
    have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega

end Nat

namespace Nat

/--
[polygonalNumber_at_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
lemma polygonalNumber_at_two
  {s : ℕ}
-- given
  (hs : 3 ≤ s) :
-- imply
  polygonalNumber s 2 = s := by
-- proof
  have hc : Nat.choose 2 2 = 1 := by decide
  simp only [polygonalNumber, hc]
  omega

end Nat

namespace Nat

/--
[polygonalNumber_at_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
lemma polygonalNumber_at_three
  {s : ℕ}
-- given
  (hs : 3 ≤ s) :
-- imply
  polygonalNumber s 3 = 3 * s - 3 := by
-- proof
  have hc : Nat.choose 3 2 = 3 := by decide
  simp only [polygonalNumber, hc]
  omega

end Nat

namespace Nat

/--
[polygonalNumber_at_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
lemma polygonalNumber_at_four
  {s : ℕ}
-- given
  (hs : 3 ≤ s) :
-- imply
  polygonalNumber s 4 = 6 * s - 8 := by
-- proof
  have hc : Nat.choose 4 2 = 6 := by decide
  simp [polygonalNumber, hc]
  omega

end Nat

namespace Nat

/--
[polygonalNumber_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
lemma polygonalNumber_three
  {n : ℕ} :
-- imply
  polygonalNumber 3 n = n * (n + 1) / 2 := by
-- proof
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  have hmul : n * (n + 1) = n ^ 2 + n := by ring
  simp [polygonalNumber]
  omega

end Nat

namespace Nat

/--
[polygonalNumber_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
lemma polygonalNumber_four
  {n : ℕ} :
-- imply
  polygonalNumber 4 n = n ^ 2 := by
-- proof
  simpa [polygonalNumber] using two_choose_add n

end Nat

namespace Nat

/--
[polygonalNumber_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
lemma polygonalNumber_five
  {n : ℕ} :
-- imply
  polygonalNumber 5 n = (3 * n ^ 2 - n) / 2 := by
-- proof
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  simp [polygonalNumber]
  omega

end Nat

namespace Nat

/--
[polygonalNumber_six](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
lemma polygonalNumber_six
  {n : ℕ} :
-- imply
  polygonalNumber 6 n = 2 * n ^ 2 - n := by
-- proof
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  simp [polygonalNumber]
  omega

end Nat

/--
[polygonalNumber_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_zero_eq
  {s : ℕ} :
-- imply
  polygonalNumber s 0 = 0 := by
-- proof
  apply Nat.polygonalNumber_zero s

/--
[polygonalNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_one_eq
  {s : ℕ} :
-- imply
  polygonalNumber s 1 = 1 := by
-- proof
  apply Nat.polygonalNumber_one s


-- created on 2026-10-20
-- updated on 2026-10-23
