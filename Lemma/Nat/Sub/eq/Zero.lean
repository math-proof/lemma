import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  [Zero Q] [SubSelf Q]
-- given
  (a : Q) :
-- imply
  a - a = 0 :=
-- proof
  SubSelf.sub_self a


-- created on 2025-10-16
