import Lemma.Set.NotIn.of.Ne
import Lemma.Set.NotIn_Union.of.NotIn.NotIn
open Set


@[main]
private lemma main
  {x y : α}
  {s : Set α}
-- given
  (h₀ : x ∉ s)
  (h₁ : x ≠ y) :
-- imply
  x ∉ s ∪ {y} := by
-- proof
  apply NotIn_Union.of.NotIn.NotIn h₀
  apply NotIn.of.Ne h₁


-- created on 2023-05-20
