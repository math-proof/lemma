import sympy.core.mul
import sympy.Basic
open Tensor


@[main]
private lemma main
  {n m : ℕ}
-- given
  (s : List ℕ)
  (hn : s.length ≤ n)
  (hm : n ≤ m) :
-- imply
  pad1 s m = List.replicate (m - n) 1 ++ pad1 s n := by
-- proof
  simp [pad1]
  have : m - s.length = m - n + (n - s.length) := by omega
  rw [this, List.replicate_add, List.append_assoc]


-- created on 2026-10-07
