import Def.Data.Tensor.Sum
import Def.Data.Tensor.Defs


@[path]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h_s : d < s.length)
  (h : d > 0)
  (X : Tensor α s) :
-- imply
  (X.sum d).length = X.length := by
-- proof
  cases s with
  | nil =>
    simp at h_s
  | cons m s =>
    cases d with
    | zero =>
      exact (Nat.not_lt_zero 0 h).elim
    | succ d =>
      rfl


-- created on 2025-06-24
-- updated on 2026-11-21
