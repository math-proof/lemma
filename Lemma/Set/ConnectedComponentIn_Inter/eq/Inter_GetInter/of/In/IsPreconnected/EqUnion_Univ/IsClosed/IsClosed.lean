import Mathlib
import sympy.Basic


/--
[connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ.lean)
-/
@[main]
private lemma main
  [TopologicalSpace X]
  {A B : Set X}
  {e : X}
-- given
  (hA : IsClosed A)
  (hB : IsClosed B)
  (hAB : A ∪ B = Set.univ)
  (hA' : IsPreconnected (A \ B))
  (he : e ∈ A \ B) :
-- imply
  connectedComponentIn (A ∩ B)ᶜ e = A ∩ (A ∩ B)ᶜ := by
-- proof
  have hcov : ∀ x, x ∈ A ∨ x ∈ B := fun x => by
    have hx : x ∈ A ∪ B := hAB ▸ Set.mem_univ x
    exact hx
  have hdiff : A \ B = A ∩ (A ∩ B)ᶜ := by
    ext x
    simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_compl_iff, not_and]
    tauto
  have heU : e ∈ (A ∩ B)ᶜ := fun h => he.2 h.2
  apply Set.Subset.antisymm
  ·
    have hsub : connectedComponentIn (A ∩ B)ᶜ e ⊆ Bᶜ ∪ Aᶜ := by
      intro x hx
      have hxU := connectedComponentIn_subset _ _ hx
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hxU
      rcases hxU with h | h
      · exact Or.inr h
      · exact Or.inl h
    have hdisj : Disjoint Bᶜ Aᶜ := by
      rw [Set.disjoint_iff]
      rintro x ⟨hxB, hxA⟩
      rcases hcov x with h | h
      · exact hxA h
      · exact hxB h
    rcases isPreconnected_connectedComponentIn.subset_or_subset hB.isOpen_compl hA.isOpen_compl hdisj hsub with h | h
    · intro x hx
      have hxB : x ∉ B := h hx
      have hxA : x ∈ A := (hcov x).resolve_right hxB
      exact ⟨hxA, fun hAB' => hxB hAB'.2⟩
    · exact absurd (h (mem_connectedComponentIn heU)) (fun h' => h' he.1)
  · rw [← hdiff]
    exact hA'.subset_connectedComponentIn he (fun x hx => fun h => hx.2 h.2)


-- created on 2026-10-05
