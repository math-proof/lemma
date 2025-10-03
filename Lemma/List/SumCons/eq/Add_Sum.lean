import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {l : List α}
  {a : α} :
-- imply
  (a :: l).sum = a + l.sum :=
-- proof
  List.sum_cons


-- created on 2024-07-01
-- updated on 2025-10-03
