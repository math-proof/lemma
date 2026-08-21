import Lemma.Int.OrAndS.NotOrAndS.is.Ge_0.Ge_0.OrLeS_0
import Lemma.Nat.Eq.of.Le.Le
open Nat Int


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
      left
      have h_eq := Eq.of.Le.Le h_le h_x
      constructor <;>
        assumption
    | inr h_le =>
      right
      have h_eq := Eq.of.Le.Le h_le h_y
      constructor <;>
        assumption
  ·
    intro h
    obtain ⟨rfl, h⟩ | ⟨rfl, h⟩ := h <;>
    ·
      simp_all


-- created on 2025-04-19
-- updated on 2025-08-03
