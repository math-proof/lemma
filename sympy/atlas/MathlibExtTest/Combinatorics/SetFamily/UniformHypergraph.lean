/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SetFamily/UniformHypergraph.lean -/


import sympy.atlas.Combinatorics.SetFamily.UniformHypergraph
import Lemma.Finset.SetFamily.UniformHypergraph


example {V : Type*} (H : Finset (Finset V)) :
    SetFamily.IsUniform H 3 ↔ ∀ e ∈ H, e.card = 3 :=
  SetFamily.isUniform_iff H 3

example {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (m k : ℕ) :
    SetFamily.ContainsSubgraph H m k ↔
      ∃ S : Finset V, S.card = m ∧ k ≤ (H.filter fun e => e ⊆ S).card :=
  SetFamily.containsSubgraph_iff H m k

example : SetFamily.IsUniform ({{0, 1}} : Finset (Finset (Fin 3))) 2 := by
  rw [SetFamily.isUniform_iff]
  decide

example : ¬ SetFamily.IsUniform ({{0, 1}} : Finset (Finset (Fin 3))) 1 := by
  rw [SetFamily.isUniform_iff]
  decide

example : SetFamily.ContainsSubgraph ({{0, 1}} : Finset (Finset (Fin 3))) 2 1 :=
  ⟨{0, 1}, by decide, by decide⟩

example : ¬ SetFamily.ContainsSubgraph ({{0, 1}} : Finset (Finset (Fin 3))) 1 1 := by
  rw [SetFamily.containsSubgraph_iff]
  rintro ⟨S, hcard, hle⟩
  have hsub : ({0, 1} : Finset (Fin 3)) ⊆ S := by
    have hfin : ({{0, 1}} : Finset (Finset (Fin 3))).filter (fun e => e ⊆ S) =
        {{0, 1}} := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      have h1 : ({{0, 1}} : Finset (Finset (Fin 3))).card = 1 := by decide
      omega
    have hmem : ({0, 1} : Finset (Fin 3)) ∈
        ({{0, 1}} : Finset (Finset (Fin 3))).filter (fun e => e ⊆ S) := by
      rw [hfin]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hmem).2
  have h2 : ({0, 1} : Finset (Fin 3)).card ≤ S.card := Finset.card_le_card hsub
  have h01 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  omega
