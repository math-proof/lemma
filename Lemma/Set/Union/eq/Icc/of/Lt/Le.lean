import sympy.sets.sets
import Lemma.Nat.Le.of.Lt
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b x : α}
-- given
  (h₀ : a < x)
  (h₁ : x ≤ b) :
-- imply
  Icc a x ∪ Ioc x b = Icc a b := by
-- proof
  apply Set.Icc_union_Ioc_eq_Icc _ h₁
  apply Le.of.Lt h₀


-- created on 2025-10-01
