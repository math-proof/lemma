import Lemma.Hyperreal.Infinite.is.All_GtAbs
open Hyperreal


@[main]
private lemma mp
  {x : ℝ*}
-- given
  (h : Infinite x) :
-- imply
  Infinite (-x) := by
-- proof
  apply Infinite.of.All_GtAbs
  intro ⟨δ, hδ⟩
  have h := All_GtAbs.of.Infinite h
  simp at ⊢ h
  exact h δ hδ


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  Infinite x ↔ Infinite (-x) := by
-- proof
  constructor
  ·
    apply mp
  ·
    intro h
    have h := mp h
    simp at h
    exact h


-- created on 2025-12-10
