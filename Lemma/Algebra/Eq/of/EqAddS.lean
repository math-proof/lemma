import Lemma.Algebra.EqSubS.of.Eq
open Algebra


@[main]
private lemma nat
  {x y d : ℕ}
-- given
  (h : x + d = y + d) :
-- imply
  x = y := by
-- proof
  have h := EqSubS.of.Eq h d
  simp_all [h]


@[main]
private lemma nat.left
  {x y d : ℕ}
-- given
  (h : d + x = d + y):
-- imply
  x = y := by
-- proof
  have h := EqSubS.of.Eq h d
  simp_all [h]


@[main]
private lemma left
  [AddGroup α]
  {x y d : α}
-- given
  (h : d + x = d + y):
-- imply
  x = y := by
-- proof
  have h := EqSubS.of.Eq h d
  simp_all [h]


@[main]
private lemma main
  [AddGroup α]
  {x y d : α}
-- given
  (h : x + d = y + d) :
-- imply
  x = y := by
-- proof
  have h := EqSubS.of.Eq h d
  simp_all [h]


-- created on 2025-03-30
