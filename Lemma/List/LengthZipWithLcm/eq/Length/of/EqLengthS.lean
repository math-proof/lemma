import Theorem.Data.List.Mul.Part4


@[path]
private lemma main
-- given
  (s s' : List ℕ)
  (h : s.length = s'.length) :
-- imply
  (s.zipWith Nat.lcm s').length = s.length := by
-- proof
  simp [List.length_zipWith, h]


-- created on 2026-10-07
