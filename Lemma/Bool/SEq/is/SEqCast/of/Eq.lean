import stdlib.SEq
import sympy.Basic

/--
debug info : using mpr.comm 1 instead of mpr.comm 2 due to the fact that:
(h : n_a = n_b')
proposition `cast (congrArg Vector h) a ≃ b` is dependent on `h`, effectively making h an implicit argument.
thus the resulted lemma name using attribute mpr.comm 1 is `Bool.SEq.of.SEq_Cast`
-/
@[main, comm, mp, mpr, mp.comm 2, mpr.comm 1]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h : n_a = n_b') :
-- imply
  a ≃ b ↔ cast (congrArg Vector h) a ≃ b := by
-- proof
  aesop


-- created on 2025-05-31
-- updated on 2025-06-28
