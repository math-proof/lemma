/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Saturation.lean -/


import Def.Combinatorics.SimpleGraph.Saturation
import Lemma.SimpleGraph.Saturation
import Mathlib.Tactic.FinCases
open SimpleGraph


/-!
# Boundary tests for graph saturation and the saturation number

Source: Huanying Bian, Qing Cui, Shengjin Ji, and Fuhong Ma,
*On the saturation number of the kite graph*, arXiv:2608.16069v1.

These tests exercise every public declaration of
`MathlibExt.Combinatorics.SimpleGraph.Saturation` against the
source-sensitive boundaries: a complete host with no missing edge, the
edgeless host saturated for the one-edge forbidden graph, and the `n = 0`
and `n = 1` vertex counts.
-/

/-- `isSaturated_def`: saturation unfolds to freeness plus maximality. -/
example {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) :
    H.IsSaturated G ↔
      H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, H.Free G' → G ≤ G' → G' ≤ G :=
  isSaturated_def H G

/-- `isSaturated_iff_forall_gt`: maximality via strict extensions. -/
example {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) :
    H.IsSaturated G ↔ H.Free G ∧ ∀ ⦃G' : SimpleGraph W⦄, G < G' → ¬ H.Free G' :=
  isSaturated_iff_forall_gt H G

/-- Boundary: the edgeless host is saturated for the one-edge forbidden graph. -/
example : (edge (0 : Fin 2) 1).IsSaturated (⊥ : SimpleGraph (Fin 2)) := by
  rw [isSaturated_iff_missing_edge]
  have hadj : (edge (0 : Fin 2) 1).Adj 0 1 :=
    (edge_adj (0 : Fin 2) 1 0 1).mpr ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩
  have hne : edge (0 : Fin 2) 1 ≠ (⊥ : SimpleGraph (Fin 2)) :=
    fun he => (bot_adj 0 1).mp (he ▸ hadj)
  refine ⟨free_bot hne, fun s t hst _ => ?_⟩
  have hsub : edge (0 : Fin 2) 1 ≤ ⊥ ⊔ edge s t := by
    fin_cases s <;> fin_cases t <;> simp_all [edge_comm]
  exact not_free.mpr (IsContained.of_le hsub)

/-- Boundary: a complete host has no missing edge. Here the one-edge graph on
`Fin 2` cannot embed into the complete graph on `Fin 1`, so freeness plus the
complete-host helper gives saturation. -/
example : (edge (0 : Fin 2) 1).IsSaturated (⊤ : SimpleGraph (Fin 1)) := by
  apply (isSaturated_top _).mpr
  intro hc
  obtain ⟨f⟩ := hc
  have hadj : (edge (0 : Fin 2) 1).Adj 0 1 :=
    (edge_adj (0 : Fin 2) 1 0 1).mpr ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩
  have hcon := f.toHom.map_adj hadj
  have e0 : f.toHom (0 : Fin 2) = (0 : Fin 1) := Subsingleton.elim _ _
  have e1 : f.toHom (1 : Fin 2) = (0 : Fin 1) := Subsingleton.elim _ _
  rw [e0, e1, top_adj] at hcon
  exact hcon rfl

/-- `isSaturated_top` with the host on its own vertex type: the forbidden
graph on `Fin 2` against the complete host on `Fin 1`. -/
example : (edge (0 : Fin 2) 1).IsSaturated (⊤ : SimpleGraph (Fin 1)) ↔
    (edge (0 : Fin 2) 1).Free (⊤ : SimpleGraph (Fin 1)) :=
  isSaturated_top (edge (0 : Fin 2) 1)

/-- Boundary `n = 0`: with the empty forbidden graph, every host contains it,
so the admissible family is empty and `sat` takes its explicit value. -/
example : (⊥ : SimpleGraph (Fin 0)).sat 0 = 0 := by
  apply sat_eq_zero_of_counts_empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro m hm
  obtain ⟨G, _, hsat, _⟩ := hm
  exact hsat.1 IsContained.of_isEmpty

/-- Boundary `n = 1`: the upper bound forces `sat` to `0` via the saturated
edgeless host. -/
example : (edge (0 : Fin 2) 1).sat 1 = 0 := by
  have hle := (edge (0 : Fin 2) 1).sat_le_card_of_isSaturated 1
    (⊥ : SimpleGraph (Fin 1)) edgeOne_saturated_bot_one
  refine Nat.le_zero.mp (hle.trans ?_)
  simp

/-- Attainment at `n = 1`: some saturated host realizes `sat`. -/
example : ∃ G : SimpleGraph (Fin 1), ∃ _ : DecidableRel G.Adj,
    (edge (0 : Fin 2) 1).IsSaturated G ∧
      G.edgeFinset.card = (edge (0 : Fin 2) 1).sat 1 := by
  apply exists_isSaturated_card_eq_sat
  exact ⟨_, ⊥, inferInstance, edgeOne_saturated_bot_one, rfl⟩

