import stdlib.SEq
import sympy.vector.vector


@[main]
private lemma main
  [AddCommMonoid α]
  {s : Finset ι}
  {x : ι → List.Vector α n}
  {y : ι → List.Vector α n'}
-- given
  (h : ∀ i ∈ s, x i ≃ y i) :
-- imply
  ∑ i ∈ s, x i ≃ ∑ i ∈ s, y i := by
-- proof
  sorry


@[main]
private lemma fin
  [AddCommMonoid α]
  {x : Fin m → List.Vector α n}
  {y : Fin m → List.Vector α n'}
-- given
  (h : ∀ i : Fin m, x i ≃ y i) :
-- imply
  ∑ i : Fin m, x i ≃ ∑ i : Fin m, y i := by
-- proof
  apply main
  aesop


-- created on 2025-11-05
