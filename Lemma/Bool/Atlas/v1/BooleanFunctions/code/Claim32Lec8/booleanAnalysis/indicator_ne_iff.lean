import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.Claim32Lec8
open BooleanAnalysis Finset


/--
[indicator_ne_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
  {x y : Fin n → Bool} :
-- imply
  indicator A x ≠ indicator A y ↔ (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) := by
-- proof
  unfold indicator
  constructor
  ·
    intro h
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp_all
  ·
    intro h
    obtain ⟨hx, hny⟩ | ⟨hnx, hy⟩ := h
    · simp [hx, hny]
    · simp [hnx, hy]



lemma BooleanAnalysis.indicator_ne_iff
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
  {x y : Fin n → Bool} :
-- imply
  indicator A x ≠ indicator A y ↔ (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
