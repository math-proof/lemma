import Lemma.Int.Sub.eq.Zero.is.Eq
open Int


@[main]
private lemma main
  [AddGroup α]
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  a - b ≠ 0 := by
-- proof
  by_contra h'
  have := Eq.of.Sub.eq.Zero h'
  contradiction


-- created on 2025-03-30
