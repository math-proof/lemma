import Lemma.Set.Eq.of.All_In.All_In
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h₀ : ∀ x, x ∈ A → x ∈ B)
  (h₁ : ∀ x, x ∈ B → x ∈ A) :
-- imply
  A = B :=
-- proof
  Eq.of.All_In.All_In h₀ h₁


-- created on 2025-07-29
