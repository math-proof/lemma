import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import sympy.stats.iterates
import sympy.Basic
open Finset Preorder


@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSpace Z] [MeasurableSpace β]
  {n m : ℕ}
  {φ : Z × S → β}
  {φ₁ : (Iic n → S) → Z}
-- given
  (h₀ : n ≤ m)
  (h₁ : Measurable φ)
  (h₂ : Measurable φ₁) :
-- imply
  Measurable (iterates_update h₀ φ φ₁) := by
-- proof
  apply h₁.comp ((h₂.comp ((measurable_frestrictLe₂ h₀).comp (measurable_frestrictLe m))).prodMk (measurable_pi_apply m))


-- created on 2026-09-26