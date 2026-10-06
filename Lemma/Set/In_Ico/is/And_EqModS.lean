import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Int.In_Range.is.Le.Lt
import Lemma.Int.In_Range.is.Mod.In_Range
open Int


@[main]
private lemma main
  {x a b d : ℤ}
-- given
  (h : 0 < d) :
-- imply
  x ∈ Range a b d ↔ a ≤ x ∧ x < b ∧ x % d = a % d := by
-- proof
  rw [In_Range.is.Mod.In_Range, EqSign_1.of.Gt_0 h, In_Range.is.Le.Lt]
  constructor
  · intro h'
    obtain ⟨hmod, hle, hlt⟩ := h'
    exact ⟨hle, hlt, hmod⟩
  · intro h'
    obtain ⟨hle, hlt, hmod⟩ := h'
    exact ⟨hmod, hle, hlt⟩


-- created on 2022-01-01
-- updated on 2023-05-30
