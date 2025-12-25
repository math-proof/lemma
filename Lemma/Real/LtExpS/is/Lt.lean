import sympy.Basic
import sympy.functions.elementary.exponential


@[main, comm, mp, mpr]
private lemma main
  [ExpPos α]
-- given
  (a b : α) :
-- imply
  exp a < exp b ↔ a < b :=
-- proof
  ExpPos.exp_lt_exp


-- created on 2025-12-25
