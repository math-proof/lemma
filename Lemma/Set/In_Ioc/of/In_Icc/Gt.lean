import Lemma.Set.In_Ioc.is.Lt.Le
import Lemma.Set.Le.of.In_Icc
open Set


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₁ : x > a)
  (h₀ : x ∈ Icc a b) :
-- imply
  x ∈ Ioc a b := by
-- proof
  apply In_Ioc.of.Lt.Le h₁
  exact Le.of.In_Icc h₀


-- created on 2018-06-21
