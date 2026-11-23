import Def.Data.Fin.Rope
import Initialize.Tactic.Attr.Basic
import Mathlib


/-- Every coordinate of `Fin (d + d)` lies in the interleaved pair \(\{2t, 2t + 1\}\). -/
@[path]
private lemma main
-- given
  (d : ℕ)
  (i : Fin (d + d)) :
-- imply
  ∃ t : Fin d, i ∈ ({t.ropeEven, t.ropeOdd} : Set (Fin (d + d))) := by
-- proof
  if h : (i : ℕ) % 2 = 0 then
    refine ⟨⟨(i : ℕ) / 2, ?_⟩, ?_⟩
    ·
      have := i.isLt
      omega
    ·
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      ext
      simp [Fin.ropeEven]
      omega
  else
    refine ⟨⟨(i : ℕ) / 2, ?_⟩, ?_⟩
    ·
      have := i.isLt
      omega
    ·
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      right
      ext
      simp [Fin.ropeOdd]
      omega


-- created on 2026-11-23
