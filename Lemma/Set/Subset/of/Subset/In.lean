import Lemma.Set.SubsetFinset.of.In
import Lemma.Set.SubsetUnionS.of.Subset.Subset
open Set


@[main]
private lemma main
  {α} {x : α} {A B : Set α}
-- given
  (h₀ : x ∈ A)
  (h₁ : B ⊆ A) :
-- imply
  B ∪ {x} ⊆ A := by
-- proof
  have h_singleton := SubsetFinset.of.In h₀
  have := SubsetUnionS.of.Subset.Subset h₁ h_singleton
  simpa using this


-- created on 2018-04-21
