/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Domination.lean -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

namespace SimpleGraph

/-- `S` dominates `G`: every vertex is in `S` or adjacent to a vertex of `S`. -/
def IsDominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v : V, v ∈ S ∨ ∃ u ∈ S, G.Adj u v

/-- `S` is an independent dominating set: independent and dominating. -/
def IsIndepDominating {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsIndepSet S ∧ G.IsDominating S

/-- The domination number: the least size of a dominating set. -/
noncomputable def dominationNumber {V : Type*} (G : SimpleGraph V)
    [Fintype V] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsDominating ↑S}

/-- The independent domination number: the least size of an independent
dominating set. -/
noncomputable def indepDominationNumber {V : Type*} (G : SimpleGraph V)
    [Fintype V] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsIndepDominating ↑S}

/-- Every finite graph has an independent dominating set. -/
theorem exists_isIndepDominating {V : Type*} (G : SimpleGraph V) [Finite V] :
    ∃ S : Finset V, G.IsIndepDominating ↑S := by
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
      rcases hx with rfl | hx
      · rcases hy with rfl | hy
        · exact hxy rfl
        · exact h' y hy hadj.symm
      · rcases hy with rfl | hy
        · exact h' x hx hadj
        · exact hS.isIndepSet hx hy hxy hadj
    have hsub : insert v (↑S : Set V) ⊆ (↑S : Set V) :=
      (hS.isMaximalIndepSet S).2 h_indep (Set.subset_insert v ↑S)
    exact hv (by simpa using hsub (Set.mem_insert v ↑S))

/-- An independent dominating set attaining the independent domination number exists. -/
theorem exists_indepDominationNumber_eq_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] :
    ∃ S : Finset V, S.card = G.indepDominationNumber ∧ G.IsIndepDominating ↑S := by
  classical
  unfold indepDominationNumber
  have hne : {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsIndepDominating ↑S}.Nonempty := by
    obtain ⟨S, hS⟩ := G.exists_isIndepDominating
    exact ⟨S.card, S, rfl, hS⟩
  simpa only [Set.mem_ofPred_eq] using Nat.sInf_mem hne

/-- Every independent dominating set has size at least the independent domination number. -/
theorem indepDominationNumber_le_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] {S : Finset V} (hS : G.IsIndepDominating ↑S) :
    G.indepDominationNumber ≤ S.card := by
  unfold indepDominationNumber
  exact Nat.sInf_le ⟨S, rfl, hS⟩

/-- A dominating set attaining the domination number exists. -/
theorem exists_dominationNumber_eq_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] :
    ∃ S : Finset V, S.card = G.dominationNumber ∧ G.IsDominating ↑S := by
  classical
  unfold dominationNumber
  have hne : {k : ℕ | ∃ S : Finset V, S.card = k ∧ G.IsDominating ↑S}.Nonempty := by
    refine ⟨Finset.univ.card, Finset.univ, rfl, ?_⟩
    intro v
    exact Or.inl (by simp)
  simpa only [Set.mem_ofPred_eq] using Nat.sInf_mem hne

/-- Every dominating set has size at least the domination number. -/
theorem dominationNumber_le_card {V : Type*} (G : SimpleGraph V)
    [Fintype V] {S : Finset V} (hS : G.IsDominating ↑S) :
    G.dominationNumber ≤ S.card := by
  unfold dominationNumber
  exact Nat.sInf_le ⟨S, rfl, hS⟩

end SimpleGraph
