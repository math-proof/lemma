import Mathlib.Analysis.Real.Hyperreal
import sympy.core.singleton
import Lemma.Int.LtAbsSub.is.LtSub.Lt_Add
open Int
open Hyperreal (IsSt)


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*)
  (a : ℝ) :
-- imply
  IsSt x a ↔ ∀ δ : ℝ⁺, |x - a| < δ := by
-- proof
  constructor
  ·
    intro h ⟨δ, hδ⟩
    simp [IsSt] at h
    apply LtAbsSub.of.LtSub.Lt_Add
    repeat grind
  ·
    intro h
    simp [IsSt]
    intro δ hδ
    have h := h ⟨δ, hδ⟩
    apply LtSub.Lt_Add.of.LtAbsSub h


-- created on 2025-12-08
