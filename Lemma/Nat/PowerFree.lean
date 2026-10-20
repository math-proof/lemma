import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PowerFree
open Nat


/--
[isPowerFree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
private lemma isPowerFree_iff_eq
  {n k : ℕ} :
-- imply
  n.IsPowerFree k ↔ 2 ≤ k ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ¬p ^ k ∣ n := by
-- proof
  apply Nat.isPowerFree_iff

/--
[IsPowerFree.two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
private lemma IsPowerFree_two_le_eq
  {n k : ℕ}
-- given
  (h : n.IsPowerFree k) :
-- imply
  2 ≤ k := by
-- proof
  apply Nat.IsPowerFree.two_le h

/--
[IsPowerFree.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
private lemma IsPowerFree_pos_eq
  {n k : ℕ}
-- given
  (h : n.IsPowerFree k) :
-- imply
  0 < n := by
-- proof
  apply Nat.IsPowerFree.pos h

/--
[IsPowerFree.not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
private lemma IsPowerFree_not_dvd_eq
  {n k p : ℕ}
-- given
  (h : n.IsPowerFree k)
  (hp : p.Prime) :
-- imply
  ¬p ^ k ∣ n := by
-- proof
  apply Nat.IsPowerFree.not_dvd h hp

/--
[IsPowerFree.of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
private lemma IsPowerFree_of_dvd_eq
  {m n k : ℕ}
-- given
  (h : n.IsPowerFree k)
  (hmn : m ∣ n) :
-- imply
  m.IsPowerFree k := by
-- proof
  apply Nat.IsPowerFree.of_dvd h hmn

/--
[IsPowerFree.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
private lemma IsPowerFree_mono_eq
  {n k l : ℕ}
-- given
  (h : n.IsPowerFree k)
  (hkl : k ≤ l) :
-- imply
  n.IsPowerFree l := by
-- proof
  apply Nat.IsPowerFree.mono h hkl

/--
[isPowerFree_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean)
-/
@[path]
private lemma isPowerFree_two_eq
  {n : ℕ} :
-- imply
  n.IsPowerFree 2 ↔ Squarefree n := by
-- proof
  apply Nat.isPowerFree_two


-- created on 2026-10-20
