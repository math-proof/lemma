import Lemma.Basic


@[main]
private lemma left.nat
  {a b : ℕ}
-- given
  (h : b + a > b) :
-- imply
  a > 0 := by
-- proof
  simp_all


@[main]
private lemma nat
  {a b : ℕ}
-- given
  (h : a + b > b) :
-- imply
  a > 0 := by
-- proof
  simp_all


@[main]
private lemma left
  [OrderedAddCommGroup α]
  {a b : α}
-- given
  (h : b + a > b) :
-- imply
  a > 0 := by
-- proof
  simp_all


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b : α}
-- given
  (h : a + b > b) :
-- imply
  a > 0 := by
-- proof
  simp_all



-- created on 2025-05-24
