import Lemma.Set.Ge.of.In_Icc
import Lemma.Set.In_Ico.is.Le.Lt
open Set


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Icc a b)
  (h₁ : x < b) :
-- imply
  x ∈ Ico a b := by
-- proof
  apply In_Ico.of.Le.Lt _ h₁
  exact Ge.of.In_Icc h₀


-- created on 2018-06-22
