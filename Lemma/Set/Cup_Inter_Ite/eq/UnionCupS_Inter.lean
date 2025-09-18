import Lemma.Set.Inter_Ite.eq.Ite_InterS
import Lemma.Set.Cup_Ite.eq.UnionCupS
open Set


@[main]
private lemma main
-- given
  (A C : Set α)
  (f g h : α → Set β)
  (h_d : (x : α) → Decidable (x ∈ C)) :
-- imply
  ⋃ x ∈ A, g x ∩ (if x ∈ C then
    f x
  else
    h x) = (⋃ x ∈ A ∩ C, g x ∩ f x) ∪ ⋃ x ∈ A \ C, g x ∩ h x := by
-- proof
  simp only [Inter_Ite.eq.Ite_InterS]
  simp [Cup_Ite.eq.UnionCupS]


-- created on 2025-08-02
