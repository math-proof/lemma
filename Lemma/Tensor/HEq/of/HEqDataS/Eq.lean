import Structure.Data.Tensor.Defs
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {s s' : List ℕ}
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s = s')
  (h : HEq A.data B.data) :
-- imply
  HEq A B := by
-- proof
  subst h_s
  apply heq_of_eq
  cases A
  cases B
  congr
  apply eq_of_heq h


-- created on 2025-07-24
-- updated on 2026-11-20
