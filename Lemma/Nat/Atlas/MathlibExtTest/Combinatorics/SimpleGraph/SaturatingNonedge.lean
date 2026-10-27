import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.MathlibExtTest.Combinatorics.SimpleGraph.SaturatingNonedge
open SimpleGraph


/--
[test_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_le
-- imply
  (⊤ : SimpleGraph (Fin 2)) ≤ (⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1 := by
-- proof
  intro a b h
  rw [top_adj] at h
  fin_cases a <;> fin_cases b
  · exact absurd rfl h
  · rw [sup_adj]
    exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩)
  · rw [sup_adj]
    exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl, rfl⟩, by decide⟩)
  · exact absurd rfl h

/--
[test_creates_copy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_creates_copy
-- imply
  IsContained (⊤ : SimpleGraph (Fin 2)) ((⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) :=
-- proof
  IsContained.of_le test_le

/--
[test_single_missing_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_single_missing_edge
-- imply
  IsSaturatingNonedge (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) (0 : Fin 2) 1 := by
-- proof
  rw [isSaturatingNonedge_iff]
  exact ⟨by decide, by decide, test_creates_copy⟩

/--
[test_symm_edge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_symm_edge
-- imply
  IsSaturatingNonedge (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) (1 : Fin 2) 0 :=
-- proof
  test_single_missing_edge.symm

/--
[test_loop_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_loop_not_adj
-- imply
  ¬(⊤ : SimpleGraph (Fin 2)).Adj (0 : Fin 2) 0 := by
-- proof
  decide

/--
[test_loop_contained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_loop_contained
-- imply
  IsContained (⊥ : SimpleGraph (Fin 2)) ((⊤ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 0) :=
-- proof
  IsContained.of_le bot_le

/--
[test_loop_rejection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_loop_rejection
-- imply
  ¬IsSaturatingNonedge (⊥ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) (0 : Fin 2) 0 :=
-- proof
  fun h => (h.ne) rfl

/--
[test_present_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_present_ne
-- imply
  (0 : Fin 2) ≠ 1 := by
-- proof
  decide

/--
[test_present_contained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_present_contained
-- imply
  IsContained (⊤ : SimpleGraph (Fin 2)) ((⊤ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) :=
-- proof
  IsContained.of_le le_sup_left

/--
[test_present_edge_rejection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_present_edge_rejection
-- imply
  ¬IsSaturatingNonedge (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) (0 : Fin 2) 1 :=
-- proof
  fun h => (h.not_adj) (by decide)

/--
[test_nocopy_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_nocopy_ne
-- imply
  (0 : Fin 2) ≠ 1 := by
-- proof
  decide

/--
[test_nocopy_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_nocopy_not_adj
-- imply
  ¬(⊥ : SimpleGraph (Fin 2)).Adj (0 : Fin 2) 1 := by
-- proof
  decide

/--
[test_nocopy_not_contained](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_nocopy_not_contained
-- imply
  ¬IsContained (⊥ : SimpleGraph (Fin 3)) ((⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) := by
-- proof
  rw [bot_isContained_iff_card_le]
  decide

/--
[test_nocopy_rejection](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_nocopy_rejection
-- imply
  ¬IsSaturatingNonedge (⊥ : SimpleGraph (Fin 3)) (⊥ : SimpleGraph (Fin 2)) (0 : Fin 2) 1 :=
-- proof
  fun h => test_nocopy_not_contained h.2.2

/--
[test_free_host](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_free_host
-- imply
  Free (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) :=
-- proof
  free_bot (by
    intro h
    have hadj : (⊤ : SimpleGraph (Fin 2)).Adj (0 : Fin 2) 1 :=
      (top_adj _ _).mpr (by decide)
    rw [h] at hadj
    exact (bot_adj _ _).mp hadj)

/--
[test_new_copy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_new_copy
-- imply
  IsContained (⊤ : SimpleGraph (Fin 2)) ((⊥ : SimpleGraph (Fin 2)) ⊔ edge (0 : Fin 2) 1) ∧ ¬IsContained (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) :=
-- proof
  IsSaturatingNonedge.newCopy_of_free _ _ test_single_missing_edge test_free_host

/--
[test_graph_eq_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_graph_eq_single
-- imply
  saturatingNonedgeGraph (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) = edge (0 : Fin 2) 1 := by
-- proof
  ext a b
  rw [saturatingNonedgeGraph_adj]
  constructor
  · intro h
    have hne : a ≠ b := h.ne
    rw [edge_adj]
    refine ⟨?_, hne⟩
    fin_cases a <;> fin_cases b <;> simp_all
  · intro h
    rw [edge_adj] at h
    obtain ⟨hmem, hne⟩ := h
    fin_cases a <;> fin_cases b
    · exact absurd rfl hne
    · exact test_single_missing_edge
    · exact test_symm_edge
    · exact absurd rfl hne
section CountOne

/--
[test_count_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_count_one
-- imply
  numSaturatingNonedges (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) = 1 := by
-- proof
  rw [numSaturatingNonedges_eq_card_edgeFinset, test_graph_eq_single]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hfin : (edge (0 : Fin 2) 1).edgeFinset = {s((0 : Fin 2), 1)} := by
    simp [edgeFinset, edgeSet_edge_of_ne h01]
  rw [hfin]
  simp
end CountOne

/--
[test_graph_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_graph_eq_empty
-- imply
  saturatingNonedgeGraph (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) = ⊥ := by
-- proof
  ext a b
  rw [saturatingNonedgeGraph_adj]
  constructor
  · intro h
    exact absurd ((top_adj a b).mpr h.ne) h.not_adj
  · intro h
    exact False.elim ((bot_adj a b).mp h)
section CountZero

/--
[test_count_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma test_count_zero
-- imply
  numSaturatingNonedges (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) = 0 := by
-- proof
  rw [numSaturatingNonedges_eq_card_edgeFinset, test_graph_eq_empty]
  simp
end CountZero


-- created on 2026-10-23
