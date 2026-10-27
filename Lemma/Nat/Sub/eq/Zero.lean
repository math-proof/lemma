import Instance.Data.Int.Integers
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Zero Q] [SubSelf Q]
-- given
  (a : Q) :
-- imply
  a - a = 0 :=
-- proof
  SubSelf.sub_self a


-- created on 2025-10-16
