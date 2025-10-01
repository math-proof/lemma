import Lemma.Set.Eq_Empty.ou.Any_In
import Lemma.Set.Inter
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ∩ B ≠ ∅) :
-- imply
  ∃ i ∈ B, i ∈ A := by
-- proof
  have h_Or := Eq_Empty.ou.Any_In (B ∩ A)
  rw [Inter.comm] at h
  simp [h] at h_Or
  assumption


-- created on 2025-10-01
