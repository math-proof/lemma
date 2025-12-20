import Lemma.Hyperreal.Setoid.is.OrAndS
open Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal (|a - b| / (1 + |a| + |b|)) := by
-- proof
  rw [Setoid.is.OrAndS]
  constructor <;>
    intro h
  .
    obtain h | h := h
    ·
      let ⟨h_a, h_b⟩ := h
      apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
      ·
        sorry
      ·
        sorry
    ·
      let ⟨h_ab, h_b⟩ := h
      if h_a : a.Infinitesimal then
        sorry
      else
        have h := EqSt.of.InfinitesimalSub h_ab
        sorry
  .
    if h_a : a.Infinitesimal then
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
      else
        sorry
    else
      simp [h_a]
      if h_b : b.Infinitesimal then
        sorry
      else
        simp [h_b]
        sorry


-- created on 2025-12-09
