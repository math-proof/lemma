import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PolygonalNumber
open Nat


/--
[two_choose_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma two_choose_add_eq
  {n : ℕ} :
-- imply
  2 * (Nat.choose n 2) + n = n ^ 2 := by
-- proof
  apply Nat.two_choose_add n

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

/--
[polygonalNumber_at_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_at_two_eq
  {s : ℕ}
-- given
  (hs : 3 ≤ s) :
-- imply
  polygonalNumber s 2 = s := by
-- proof
  apply Nat.polygonalNumber_at_two s hs

/--
[polygonalNumber_at_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_at_three_eq
  {s : ℕ}
-- given
  (hs : 3 ≤ s) :
-- imply
  polygonalNumber s 3 = 3 * s - 3 := by
-- proof
  apply Nat.polygonalNumber_at_three s hs

/--
[polygonalNumber_at_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_at_four_eq
  {s : ℕ}
-- given
  (hs : 3 ≤ s) :
-- imply
  polygonalNumber s 4 = 6 * s - 8 := by
-- proof
  apply Nat.polygonalNumber_at_four s hs

/--
[polygonalNumber_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_three_eq
  {n : ℕ} :
-- imply
  polygonalNumber 3 n = n * (n + 1) / 2 := by
-- proof
  apply Nat.polygonalNumber_three n

/--
[polygonalNumber_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_four_eq
  {n : ℕ} :
-- imply
  polygonalNumber 4 n = n ^ 2 := by
-- proof
  apply Nat.polygonalNumber_four n

/--
[polygonalNumber_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_five_eq
  {n : ℕ} :
-- imply
  polygonalNumber 5 n = (3 * n ^ 2 - n) / 2 := by
-- proof
  apply Nat.polygonalNumber_five n

/--
[polygonalNumber_six](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean)
-/
@[path]
private lemma polygonalNumber_six_eq
  {n : ℕ} :
-- imply
  polygonalNumber 6 n = 2 * n ^ 2 - n := by
-- proof
  apply Nat.polygonalNumber_six n


-- created on 2026-10-20
