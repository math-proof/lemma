import Initialize.Tactic.Attr.Basic
import Mathlib


/-- Every index of `Fin (d + d)` is one of the two coordinates `t.castAdd d`, `t.natAdd d`. -/
@[path]
private lemma main
  {d : ℕ}
-- given
  (i : Fin (d + d)) :
-- imply
  ∃ t : Fin d, i ∈ ({t.castAdd d, t.natAdd d} : Set (Fin (d + d))) := by
-- proof
  if h : (i : ℕ) < d then
    refine ⟨⟨(i : ℕ), h⟩, ?_⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl rfl
  else
    refine ⟨⟨(i : ℕ) - d, ?_⟩, ?_⟩
    ·
      have := i.isLt
      omega
    ·
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      refine Or.inr ?_
      ext
      simp [Fin.natAdd]
      omega


-- created on 2026-11-25
