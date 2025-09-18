import Lemma.Set.NotIn.of.Ne
import Lemma.Set.NotIn_Union.of.NotIn.NotIn
import Lemma.Set.UnionSingletonS.eq.Finset
open Set


@[main]
private lemma main
  {x a b : α}
-- given
  (h₀ : x ≠ a)
  (h₁ : x ≠ b) :
-- imply
  x ∉ ({a, b} : Set α) := by
-- proof
  have h₀ := NotIn.of.Ne h₀
  have h₁ := NotIn.of.Ne h₁
  have := NotIn_Union.of.NotIn.NotIn h₀ h₁
  -- Use the fact that {a, b} is equivalent to {a} ∪ {b} to rewrite the goal
  rw [UnionSingletonS.eq.Finset] at this
  assumption


-- created on 2025-04-04
