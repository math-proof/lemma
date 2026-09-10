import Lemma.Set.NotIn.of.Ne
import Lemma.Set.NotIn_Union.of.NotIn.NotIn
open Set


@[main]
private lemma main
  {x y : α}
  {s : Set α}
-- given
  (h₀ : x ≠ y)
  (h₁ : x ∉ s) :
-- imply
  x ∉ s ∪ {y} := by
-- proof
  apply NotIn_Union.of.NotIn.NotIn h₁
  apply NotIn.of.Ne h₀


-- created on 2023-05-20
