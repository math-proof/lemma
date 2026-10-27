import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter3.RandomGreedyColoring.StructuralLemma
open Finset Fintype TwoColorableHypergraph


namespace TwoColorableHypergraph

/--
[greedyCol_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/RandomGreedyColoring/StructuralLemma.lean)
-/
@[path]
lemma greedyCol_eq
  [Fintype V]
  [DecidableEq V]
  {σ : V → ℕ}
  {H : Hypergraph V}
  {v : V}
-- given
  (hσ : Function.Injective σ) :
-- imply
  greedyCol σ hσ H v = if ∃ e ∈ H, v ∈ e ∧ (∀ u ∈ e, σ u ≤ σ v) ∧ (∀ u ∈ e, σ u < σ v → greedyCol σ hσ H u = true) then false else true := by
-- proof
  unfold greedyCol
  rw [WellFounded.fix_eq]

end TwoColorableHypergraph

namespace TwoColorableHypergraph

/--
[greedyCol_false_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/RandomGreedyColoring/StructuralLemma.lean)
-/
@[path]
lemma greedyCol_false_iff
  [Fintype V]
  [DecidableEq V]
  {σ : V → ℕ}
  {H : Hypergraph V}
  {v : V}
-- given
  (hσ : Function.Injective σ) :
-- imply
  greedyCol σ hσ H v = false ↔ ∃ e ∈ H, v ∈ e ∧ (∀ u ∈ e, σ u ≤ σ v) ∧ (∀ u ∈ e, σ u < σ v → greedyCol σ hσ H u = true) := by
-- proof
  constructor
  · intro h
    rw [greedyCol_eq] at h
    split_ifs at h with hcond
    · exact hcond
  · intro h
    rw [greedyCol_eq]
    simp only [h, ite_true]

end TwoColorableHypergraph

namespace TwoColorableHypergraph

/--
[greedyCol_no_all_true](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/RandomGreedyColoring/StructuralLemma.lean)
-/
@[path]
lemma greedyCol_no_all_true
  [Fintype V]
  [DecidableEq V]
  {σ : V → ℕ}
  {H : Hypergraph V}
  {k : ℕ}
  {e : Finset V}
-- given
  (hσ : Function.Injective σ)
  (hk : 2 ≤ k)
  (huni : IsKUniform H k)
  (he : e ∈ H) :
-- imply
  ¬(∀ v ∈ e, greedyCol σ hσ H v = true) := by
-- proof
  intro hall
  have hcard : e.card = k := huni e he
  have hne : e.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h, Finset.card_empty] at hcard; omega
  obtain ⟨v, hve, hvmax⟩ := e.exists_max_image σ hne
  have hpred : ∀ u ∈ e, σ u < σ v → greedyCol σ hσ H u = true :=
    fun u hu _ => hall u hu
  have hcond : ∃ e' ∈ H, v ∈ e' ∧ (∀ u ∈ e', σ u ≤ σ v) ∧
    (∀ u ∈ e', σ u < σ v → greedyCol σ hσ H u = true) :=
    ⟨e, he, hve, hvmax, hpred⟩
  have hfalse : greedyCol σ hσ H v = false := by
    rw [greedyCol_eq]; simp only [hcond, ite_true]
  exact absurd (hall v hve) (by rw [hfalse]; decide)

end TwoColorableHypergraph

namespace TwoColorableHypergraph

/--
[two_colorable_of_no_conflicting_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/RandomGreedyColoring/StructuralLemma.lean)
-/
@[path]
lemma two_colorable_of_no_conflicting_pair
  [Fintype V]
  [DecidableEq V]
  {H : Hypergraph V}
  {k : ℕ}
  {σ : V → ℕ}
-- given
  (hk : 2 ≤ k)
  (huni : IsKUniform H k)
  (hσ : Function.Injective σ)
  (hno_conflict : ¬HasConflictingPair H σ) :
-- imply
  IsTwoColorable H := by
-- proof
  classical
  use greedyCol σ hσ H
  intro e he hmono
  cases hmono with
  | inl hall_true =>
    exact greedyCol_no_all_true σ hσ H k hk huni e he hall_true
  | inr hall_false =>
    have hcard : e.card = k := huni e he
    have hne : e.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h; rw [h, Finset.card_empty] at hcard; omega
    obtain ⟨w, hwe, hwmin⟩ := e.exists_min_image σ hne
    have hw_false : greedyCol σ hσ H w = false := hall_false w hwe
    rw [greedyCol_false_iff] at hw_false
    obtain ⟨e', he', hwe', hmax', hpred'⟩ := hw_false
    exfalso
    apply hno_conflict
    unfold HasConflictingPair
    refine ⟨e', he', e, he, w, ?_, ?_, ?_⟩
    · exact ⟨hwe', hmax'⟩
    · exact ⟨hwe, hwmin⟩
    · ext x
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro ⟨hxe', hxe⟩
        have h1 : σ x ≤ σ w := hmax' x hxe'
        have h2 : σ w ≤ σ x := hwmin x hxe
        exact hσ (le_antisymm h1 h2)
      · intro hxw
        subst hxw
        exact ⟨hwe', hwe⟩

end TwoColorableHypergraph


-- created on 2026-10-23
