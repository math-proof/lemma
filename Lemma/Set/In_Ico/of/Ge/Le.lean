import Lemma.Nat.Lt_Add_1.of.Le
import Lemma.Set.In_Ico.is.Le.Lt
open Set Nat


@[main]
private lemma main
  [IntegerRing Z]
  {x a b : Z}
-- given
  (h₀ : x ≥ b)
  (h₁ : x ≤ a) :
-- imply
  x ∈ Ico b (a + 1) :=
-- proof
  In_Ico.of.Le.Lt h₀ (Lt_Add_1.of.Le h₁)


-- created on 2026-08-03
