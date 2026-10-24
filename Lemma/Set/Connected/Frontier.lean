import Mathlib
import sympy.Basic
open Set Topology


/--
[IsPreconnected.inter_frontier_nonempty_of_inter_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Connected/Frontier.lean)
-/
@[path]
lemma IsPreconnected.inter_frontier_nonempty_of_inter_compl
  [TopologicalSpace α]
  {s A : Set α}
-- given
  (hs : IsPreconnected s)
  (hA : (s ∩ A).Nonempty)
  (hAc : (s ∩ Aᶜ).Nonempty) :
-- imply
  (s ∩ frontier A).Nonempty := by
-- proof
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsub : s ⊆ interior A ∪ interior Aᶜ := by
    intro x hx
    by_contra hx_not
    rw [Set.mem_union] at hx_not
    push Not at hx_not
    have hfr : x ∈ frontier A := by
      simp only [frontier, Set.mem_sdiff]
      refine ⟨?_, hx_not.1⟩
      rw [mem_closure_iff]
      intro U hU hxU
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hx_not.2
      apply interior_maximal _ hU hxU
      intro y hy
      simp only [Set.mem_compl_iff]
      intro hyA
      exact absurd (show y ∈ U ∩ A from ⟨hy, hyA⟩) (by rw [hemp]; exact notMem_empty y)
    have : x ∈ s ∩ frontier A := ⟨hx, hfr⟩
    rw [hempty] at this
    exact notMem_empty x this
  have h1 : (s ∩ interior A).Nonempty := by
    obtain ⟨x, hxs, hxA⟩ := hA
    obtain h | h := hsub hxs
    · exact ⟨x, hxs, h⟩
    · exact absurd hxA (interior_subset h)
  have h2 : (s ∩ interior Aᶜ).Nonempty := by
    obtain ⟨x, hxs, hxAc⟩ := hAc
    obtain h | h := hsub hxs
    · exact absurd (interior_subset h) hxAc
    · exact ⟨x, hxs, h⟩
  obtain ⟨x, _, hx1, hx2⟩ := hs _ _ isOpen_interior isOpen_interior hsub h1 h2
  exact interior_subset hx2 (interior_subset hx1)


-- created on 2026-10-20
-- updated on 2026-10-23
