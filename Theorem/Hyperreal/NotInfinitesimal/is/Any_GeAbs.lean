module

public import Theorem.Bool.NotAll.is.Any_Not
public import Theorem.Hyperreal.Infinitesimal.is.All_LtAbs

public section

open Hyperreal Bool


@[comm, mp, mpr]
public theorem Hyperreal.NotInfinitesimal.is.Any_GeAbs
-- given
  (x : ℝ*) :
-- imply
  ¬x → 0 ↔ ∃ δ : ℝ⁺, |x| ≥ δ := by
-- proof
  rw [Infinitesimal.is.All_LtAbs]
  simp [NotAll.is.Any_Not]


-- created on 2025-12-09
-- updated on 2025-12-16
