import stdlib.SEq
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.SEqCast.of.Eq |
| comm | Bool.SEq_Cast.of.Eq |
-/
@[path, comm]
private lemma main
  {Vector : α → Sort v}
-- given
  (h : n = n')
  (a : Vector n) :
-- imply
  cast (congrArg Vector h) a ≃ a := by
-- proof
  simp_all [SEq]


-- created on 2025-07-25
