import Lemma.Algebra.OrAndS.NotOrAndS.is.Ge_0.Ge_0.OrLeS_0
import Lemma.Nat.Eq.of.Le.Ge
open Algebra Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (x y : α) :
-- imply
  (x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) ∧ ¬(x > 0 ∧ y > 0 ∨ x < 0 ∧ y < 0) ↔ x = 0 ∧ y ≥ 0 ∨ y = 0 ∧ x ≥ 0 := by
-- proof
  rw [OrAndS.NotOrAndS.is.Ge_0.Ge_0.OrLeS_0]
  constructor
  ·
    intro ⟨h_x, h_y, h_xy⟩
    cases h_xy with
    | inl h_le =>
      -- Case: x ≤ 0
      left
      -- Since x ≥ 0 and x ≤ 0, x must be 0
      have h_eq := Eq.of.Le.Ge h_le h_x
      constructor <;>
        assumption
    | inr h_le =>
      -- Case: y ≤ 0
      right
      -- Since y ≥ 0 and y ≤ 0, y must be 0
      have h_eq := Eq.of.Le.Ge h_le h_y
      constructor <;>
        assumption
  ·
    intro h
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    ·
      simp_all


-- created on 2025-04-19
-- updated on 2025-08-03
