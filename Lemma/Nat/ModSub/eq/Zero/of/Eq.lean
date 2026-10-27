import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [IntegerRing Z]
  {a b d : Z}
-- given
  (h : a = b) :
-- imply
  (a - b) % d = 0 := by
-- proof
  rw [h, SubSelf.sub_self, IntegerRing.zero_mod]


-- created on 2018-11-23
-- updated on 2026-10-26
