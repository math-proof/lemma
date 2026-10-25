import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Combinatorics.SimpleGraph.Saturation
open SimpleGraph


/--
[edgeOne_saturated_bot_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Saturation.lean)
-/
@[path]
lemma edgeOne_saturated_bot_one
-- imply
  (edge (0 : Fin 2) 1).IsSaturated (⊥ : SimpleGraph (Fin 1)) := by
-- proof
  rw [isSaturated_iff_missing_edge]
  have hadj : (edge (0 : Fin 2) 1).Adj 0 1 :=
    (edge_adj (0 : Fin 2) 1 0 1).mpr ⟨Or.inl ⟨rfl, rfl⟩, by decide⟩
  have hne : edge (0 : Fin 2) 1 ≠ (⊥ : SimpleGraph (Fin 2)) :=
    fun he => (bot_adj 0 1).mp (he ▸ hadj)
  refine ⟨free_bot hne, fun s t hst _ => ?_⟩
  exact absurd (Subsingleton.elim s t) hst


-- created on 2026-10-23
