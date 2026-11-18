module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Hyperreal.Infinitesimal.is.All_LtAbs

public section

open Hyperreal


@[comm, mp, mpr]
public theorem Hyperreal.IsSt.is.All_LtAbs
-- given
  (x : ℝ*)
  (r : ℝ) :
-- imply
  ((x - r) → 0) ↔ ∀ δ : ℝ⁺, |x - r| < δ := by
-- proof
  rw [Infinitesimal.is.All_LtAbs]


-- created on 2025-12-08
