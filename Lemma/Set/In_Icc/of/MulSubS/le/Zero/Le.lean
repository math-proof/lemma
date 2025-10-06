import Lemma.Algebra.OrAndSLe_0Ge_0.of.Mul.le.Zero
import Lemma.Algebra.Le.of.Sub.le.Zero
import Lemma.Algebra.Ge.of.Sub.ge.Zero
import Lemma.Set.In_Icc.of.Le.Ge
import Lemma.Algebra.Ge.of.Ge.Ge
import Lemma.Algebra.Eq.of.Ge.Le
import Lemma.Set.In_Icc.of.Ge.Le
open Algebra Set


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
  rcases h_Or with h_And | h_And
  ·
    let ⟨h_Le, h_Ge⟩ := h_And
    have h_Le := Le.of.Sub.le.Zero h_Le
    have h_Ge := Ge.of.Sub.ge.Zero h_Ge
    have := Ge.of.Ge.Ge h_Le h_Ge
    have := Eq.of.Ge.Le this h₁
    apply In_Icc.of.Le.Ge
    ·
      rwa [← this]
    ·
      rwa [this]
  ·
    let ⟨h_Le, h_Ge⟩ := h_And
    have h_Le := Le.of.Sub.le.Zero h_Le
    have h_Ge := Ge.of.Sub.ge.Zero h_Ge
    apply In_Icc.of.Ge.Le h_Ge h_Le


-- created on 2025-03-30
-- updated on 2025-03-30
