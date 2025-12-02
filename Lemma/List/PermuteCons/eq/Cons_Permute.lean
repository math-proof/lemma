import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
open List


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (s₀ : α)
  (d : ℕ) :
-- imply
  (s₀ :: s).permute ⟨i + 1, by simp⟩ d = s₀ :: s.permute i d := by
-- proof
  simp [Permute.eq.Append_AppendRotateTakeDrop]


-- created on 2025-10-31
