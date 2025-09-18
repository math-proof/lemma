import Lemma.Set.In_Union.of.In
open Set


@[main]
private lemma main
  {A B C : Set α} :
-- imply
  (A ∪ B) \ C = (A \ C) ∪ (B \ C) := by
-- proof
  ext x
  constructor <;> intro h
  ·
    let ⟨hAB, hC⟩ := h
    obtain hA | hB := hAB
    ·
      apply In_Union.of.In (B := B \ C)
      simp [hA, hC]
    ·
      apply In_Union.of.In (B := A \ C) (left := true)
      simp [hB, hC]
  ·
    obtain hAC | hBC := h
    ·
      let ⟨hA, hC⟩ := hAC
      constructor
      ·
        apply In_Union.of.In hA B
      ·
        assumption
    ·
      let ⟨hB, hC⟩ := hBC
      constructor
      ·
        apply In_Union.of.In hB A (left := true)
      ·
        assumption


-- created on 2025-04-06
