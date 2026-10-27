import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  (x : α) :
-- imply
  fract x = x - ⌊x⌋ :=
-- proof
  rfl


-- created on 2018-05-06
