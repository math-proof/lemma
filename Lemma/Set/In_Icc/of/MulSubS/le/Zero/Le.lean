import Lemma.Int.OrAndSLe_0Ge_0.of.Mul.le.Zero
import Lemma.Int.Ge0Sub.is.Le
import Lemma.Int.Le0Sub.is.Ge
import Lemma.Set.In_Icc.is.Le.Le
import Lemma.Nat.Ge.of.Ge.Ge
import Lemma.Nat.Eq.of.Ge.Le
import Lemma.Set.In_Icc.is.Le.Le
open Set Nat Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : (x - a) * (x - b) ≤ 0)
  (h₁ : a ≤ b) :
-- imply
  x ∈ Icc a b := by
-- proof
  -- Split the proof into two parts: proving a ≤ x and x ≤ b
  have h_Or := OrAndSLe_0Ge_0.of.Mul.le.Zero h₀
  obtain h_And | h_And := h_Or
  ·
    let ⟨h_Le, h_Ge⟩ := h_And
    have h_Le := Le.of.Ge0Sub h_Le
    have h_Ge := Ge.of.Le0Sub h_Ge
    have := Ge.of.Ge.Ge h_Le h_Ge
    have := Eq.of.Ge.Le this h₁
    apply In_Icc.of.Le.Le
    ·
      rwa [this]
    ·
      rwa [← this]
  ·
    let ⟨h_Le, h_Ge⟩ := h_And
    have h_Le := Le.of.Ge0Sub h_Le
    have h_Ge := Ge.of.Le0Sub h_Ge
    apply In_Icc.of.Le.Le h_Ge h_Le


-- created on 2025-03-30
-- updated on 2025-03-30
