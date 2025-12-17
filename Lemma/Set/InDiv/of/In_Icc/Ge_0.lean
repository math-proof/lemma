import Lemma.Set.In_Icc.is.Le.Le
import Lemma.Set.Ge.of.In_Icc
import Lemma.Set.Le.of.In_Icc
import Lemma.Rat.LeDivS.of.Le.Ge_0
open Set Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : x ∈ Icc a b)
  (h₁ : d ≥ 0) :
-- imply
  x / d ∈ Icc (a / d) (b / d) := by
-- proof
  have h_Ge := Ge.of.In_Icc h₀
  have h_Ge := GeDivS.of.Ge.Ge_0 h_Ge h₁
  have h_Le := Le.of.In_Icc h₀
  have h_Ge := LeDivS.of.Le.Ge_0 h_Le h₁
  apply In_Icc.of.Le.Le <;> assumption


-- created on 2025-03-01
