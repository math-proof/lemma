/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Expander.lean -/


import Def.Combinatorics.SimpleGraph.Expander
import Lemma.SimpleGraph.Expander
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega


namespace SimpleGraph.ExpanderTest

example : (1 : Fin 4) ∈
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0} := by
  simp only [SimpleGraph.mem_externalNeighborSet]
  exact ⟨by decide, 0, by decide, by decide⟩

example : (0 : Fin 4) ∉
    (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0} := by
  simp only [SimpleGraph.mem_externalNeighborSet, not_and]
  intro h _
  exact h (by decide)

example : Disjoint
    ((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}) {0} :=
  SimpleGraph.externalNeighborSet_disjoint _ _

example : ∃ a ∈ ({0, 2} : Set (Fin 4)),
    (SimpleGraph.completeGraph (Fin 4)).Adj a 1 := by
  have hmem : (1 : Fin 4) ∈
      (SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0, 2} := by
    simp only [SimpleGraph.mem_externalNeighborSet]
    exact ⟨by decide, 0, by decide, by decide⟩
  exact SimpleGraph.exists_adj_of_mem_externalNeighborSet _ hmem

example : 0 < (1 : ℝ) := four_expander.pos

example :
    (1 : ℝ) * ((({0} : Set (Fin 4)).ncard : ℝ)) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet {0}).ncard :
        ℝ)) := by
  apply four_expander.small_expansion
  rw [card_threshold]
  have e0 : ((({0} : Set (Fin 4)).ncard : ℝ)) = 1 := by
    simp [Set.ncard_singleton]
  rw [e0]
  norm_num

example : ∃ a ∈ ({0, 1} : Set (Fin 4)), ∃ b ∈ ({2, 3} : Set (Fin 4)),
    (SimpleGraph.completeGraph (Fin 4)).Adj a b := by
  apply four_expander.large_edge
  · rw [Set.disjoint_left]
    intro x hx hx2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx2
    rcases hx with rfl | rfl <;> rcases hx2 with h | h <;>
      exact absurd h (by decide)
  · rw [card_threshold]
    have e01 : (({0, 1} : Set (Fin 4)).ncard) = 2 :=
      Set.ncard_pair (by decide)
    rw [e01]
    norm_num
  · rw [card_threshold]
    have e23 : (({2, 3} : Set (Fin 4)).ncard) = 2 :=
      Set.ncard_pair (by decide)
    rw [e23]
    norm_num

example (h : ℝ) (hh : (SimpleGraph.completeGraph (Fin 4)).IsUniformVertexExpander h) :
    0 < h :=
  hh.pos

example (h : ℝ) (hh : (SimpleGraph.completeGraph (Fin 4)).IsUniformVertexExpander h)
    (S : Set (Fin 4)) (hS : (S.ncard : ℝ) ≤ (Nat.card (Fin 4) : ℝ) / 2) :
    h * (S.ncard : ℝ) ≤
      ((((SimpleGraph.completeGraph (Fin 4)).externalNeighborSet S).ncard : ℝ)) :=
  hh.small_expansion (SimpleGraph.completeGraph (Fin 4)) S hS

end SimpleGraph.ExpanderTest
