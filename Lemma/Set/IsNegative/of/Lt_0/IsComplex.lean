import Lemma.Set.IsNegative.of.Lt_0
open Set
open scoped ComplexOrder


@[main]
private lemma main
  {x : ℂ}
-- given
  (h₀ : x < 0)
  (_h₁ : x ∈ (Set.univ : Set ℂ)) :
-- imply
  x ∈ Complex.ofReal '' Set.Iio 0 :=
-- proof
  IsNegative.of.Lt_0 h₀


-- created on 2023-05-03
