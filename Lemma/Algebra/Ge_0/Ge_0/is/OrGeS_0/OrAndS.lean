import Lemma.Algebra.NotLt.of.Ge
open Algebra


@[main, mp, mpr]
private lemma main
  [LinearOrderedRing α]
-- given
  (x y : α) :
-- imply
  x ≥ 0 ∧ y ≥ 0 ↔ (x ≥ 0 ∨ y ≥ 0) ∧ (x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) := by
-- proof
  constructor
  ·
    intros
    aesop
  ·
    rintro ⟨hx | hy, ⟨h_x, h_y⟩ | ⟨h_x, h_y⟩⟩
    ·
      aesop
    ·
      have hx := NotLt.of.Ge hx
      contradiction
    ·
      aesop
    ·
      have hy := NotLt.of.Ge hy
      contradiction


-- created on 2025-04-18
-- updated on 2025-08-03
