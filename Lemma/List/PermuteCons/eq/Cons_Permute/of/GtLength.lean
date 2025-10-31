import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
open List


@[main]
private lemma main
  {s : List α}
  {i d : ℕ}
-- given
  (h : s.length > i) :
-- imply
  (s₀ :: s).permute ⟨i + 1, by simp; grind⟩ d = s₀ :: s.permute ⟨i, h⟩ d := by
-- proof
  simp [Permute.eq.Append_AppendRotateTakeDrop]


-- created on 2025-10-31
