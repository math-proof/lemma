import Lemma.Algebra.LtSubS.of.Lt
import Lemma.Algebra.Add
open Algebra


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  a < c - b :=
-- proof
  Nat.lt_sub_of_add_lt h


@[main]
private lemma left.nat
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  b < c - a := by
-- proof
  rw [Add.comm] at h
  apply Nat.lt_sub_of_add_lt h


@[main]
private lemma left
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b < c) :
-- imply
  b < c - a := by
-- proof
  have h := LtSubS.of.Lt h a
  simp at h
  exact h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b < c) :
-- imply
  a < c - b := by
-- proof
  have h := LtSubS.of.Lt h b
  simp at h
  exact h


-- created on 2024-11-27
-- updated on 2025-05-04
