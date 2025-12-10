import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
open Hyperreal


private lemma mp
  {x : ℝ*}
-- given
  (h : Infinitesimal x) :
-- imply
  Infinitesimal (-x) := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  intro ⟨δ, hδ⟩
  have h := All_LtAbs.of.Infinitesimal h
  simp at ⊢ h
  exact h δ hδ


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  Infinitesimal x ↔ Infinitesimal (-x) := by
-- proof
  constructor
  ·
    intro h
    apply mp h
  ·
    intro h
    have h := mp h
    simp at h
    assumption


-- created on 2025-12-09
