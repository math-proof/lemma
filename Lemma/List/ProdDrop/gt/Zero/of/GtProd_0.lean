import Lemma.Set.In_Append.of.In
import Lemma.List.EqProd_0.is.In0
open Set List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s.prod > 0)
  (d : ℕ) :
-- imply
  (s.drop d).prod > 0 := by
-- proof
  by_contra h'
  simp at h'
  have := In_Append.of.In h' (s.take d)
  simp at this
  have := EqProd_0.of.In0 this
  rw [this] at h
  contradiction


-- created on 2025-07-08
-- updated on 2025-08-02
