import stdlib.SEq
import sympy.Basic

/--
| attributes | lemma |
| --- | --- |
| main | Bool.SEq.is.SEqCast.of.Eq |
| comm | Bool.SEqCast.is.SEq.of.Eq |
| mp  | Bool.SEqCast.of.SEq.Eq |
| mpr   | Bool.SEq.of.SEqCast.Eq |
| mp.comm | Bool.SEq_Cast.of.SEq.Eq |
| mpr.comm | Bool.SEq.of.SEq_Cast |
| comm.is 1 | Bool.SEq.is.SEq_Cast.of.Eq |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is 1]
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
