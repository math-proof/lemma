import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Domination
open SimpleGraph


namespace SimpleGraph

/--
[exists_isIndepDominating](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
lemma exists_isIndepDominating
  [Finite V]
  {G : SimpleGraph V} :
-- imply
  ∃ S : Finset V, G.IsIndepDominating ↑S := by
-- proof
  classical
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  refine ⟨S, hS.isIndepSet, ?_⟩
  intro v
  by_cases hv : v ∈ S
  · exact Or.inl (by simpa using hv)
  · right
    by_contra h
    have h' : ∀ u ∈ (↑S : Set V), ¬ G.Adj u v := by
      intro u hu hadj
      exact h ⟨u, hu, hadj⟩
    have h_indep : G.IsIndepSet (insert v (↑S : Set V)) := by
      rw [isIndepSet_iff]
      intro x hx y hy hxy hadj
      rw [Set.mem_insert_iff] at hx hy
      obtain rfl | hx := hx
      · rcases hy with rfl | hy
        · exact hxy rfl
        · exact h' y hy hadj.symm
      · rcases hy with rfl | hy
        · exact h' x hx hadj
        · exact hS.isIndepSet hx hy hxy hadj
    have hsub : insert v (↑S : Set V) ⊆ (↑S : Set V) :=
      (hS.isMaximalIndepSet S).2 h_indep (Set.subset_insert v ↑S)
    exact hv (by simpa using hsub (Set.mem_insert v ↑S))

end SimpleGraph

namespace SimpleGraph

/--
[exists_indepDominationNumber_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
lemma exists_indepDominationNumber_eq_card
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  ∃ S : Finset V, S.card = G.indepDominationNumber ∧ G.IsIndepDominating ↑S := by
-- proof
  classical
  unfold indepDominationNumber
  have hne : {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsIndepDominating ↑S}.Nonempty := by
    obtain ⟨S, hS⟩ := G.exists_isIndepDominating
    exact ⟨S.card, S, rfl, hS⟩
  simpa only [Set.mem_ofPred_eq] using Nat.sInf_mem hne

end SimpleGraph

namespace SimpleGraph

/--
[indepDominationNumber_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
lemma indepDominationNumber_le_card
  [Fintype V]
  {G : SimpleGraph V}
  {S : Finset V}
-- given
  (hS : G.IsIndepDominating ↑S) :
-- imply
  G.indepDominationNumber ≤ S.card := by
-- proof
  unfold indepDominationNumber
  exact Nat.sInf_le ⟨S, rfl, hS⟩

end SimpleGraph

namespace SimpleGraph

/--
[exists_dominationNumber_eq_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
lemma exists_dominationNumber_eq_card
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  ∃ S : Finset V, S.card = G.dominationNumber ∧ G.IsDominating ↑S := by
-- proof
  classical
  unfold dominationNumber
  have hne : {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsDominating ↑S}.Nonempty := by
    refine ⟨Finset.univ.card, Finset.univ, rfl, ?_⟩
    intro v
    exact Or.inl (by simp)
  simpa only [Set.mem_ofPred_eq] using Nat.sInf_mem hne

end SimpleGraph

namespace SimpleGraph

/--
[dominationNumber_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean)
-/
@[path]
lemma dominationNumber_le_card
  [Fintype V]
  {G : SimpleGraph V}
  {S : Finset V}
-- given
  (hS : G.IsDominating ↑S) :
-- imply
  G.dominationNumber ≤ S.card := by
-- proof
  unfold dominationNumber
  exact Nat.sInf_le ⟨S, rfl, hS⟩

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
