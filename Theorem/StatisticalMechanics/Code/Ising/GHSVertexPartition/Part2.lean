/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Walls.ghysupermult.Part2
import Def.StatisticalMechanics.Code.Ising.GHSVertexPartition
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


lemma ghsvp_vertexEdges_mono (E : Finset (Sym2 W)) :
    Monotone (ghsvp_vertexEdges E) := by
  intro S T hST e he
  rw [ghsvp_vertexEdges, Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun x hx => hST (he.2 x hx)⟩

lemma ghsvp_vertexEdges_inter (E : Finset (Sym2 W)) (S T : Finset W) :
    ghsvp_vertexEdges E (S ∩ T) = ghsvp_vertexEdges E S ∩ ghsvp_vertexEdges E T := by
  ext e
  induction e with
  | h a b => simp [ghsvp_vertexEdges, Sharpness.edgeInside, and_assoc, and_left_comm, and_comm]

lemma ghsvp_vertexEdges_union_subset (E : Finset (Sym2 W)) (S T : Finset W) :
    ghsvp_vertexEdges E S ∪ ghsvp_vertexEdges E T ⊆ ghsvp_vertexEdges E (S ∪ T) :=
  Finset.union_subset ((ghsvp_vertexEdges_mono E) Finset.subset_union_left)
    ((ghsvp_vertexEdges_mono E) Finset.subset_union_right)


theorem ghsvp_vertexZ_logSupermodular (E : Finset (Sym2 W)) (J : Sym2 W -> Real)
    (hJ : forall e, 0 <= J e) (hnd : ∀ e ∈ E, ¬ e.IsDiag) (S T : Finset W) :
    ghsvp_vertexZ E J S * ghsvp_vertexZ E J T <=
      ghsvp_vertexZ E J (S ∪ T) * ghsvp_vertexZ E J (S ∩ T) := by
  unfold ghsvp_vertexZ
  let ES := ghsvp_vertexEdges E S
  let ET := ghsvp_vertexEdges E T
  have hlat := ghsvp_ZJ_zero_logSupermodular J hJ ES ET (by
    intro e he
    rw [Finset.mem_union] at he
    exact he.elim (fun h => hnd e (Finset.mem_filter.mp h).1)
      (fun h => hnd e (Finset.mem_filter.mp h).1))
  have hmono := ghsvp_ZJ_zero_mono J hJ (ES ∪ ET)
    (ghsvp_vertexEdges E (S ∪ T)) (ghsvp_vertexEdges_union_subset E S T) (by
      intro e he
      exact hnd e (Finset.mem_filter.mp he).1)
  dsimp [ES, ET] at hlat hmono
  rw [← ghsvp_vertexEdges_inter] at hlat
  have hz : 0 <= ZJ (ghsvp_vertexEdges E (S ∩ T)) J (fun _ => 0) :=
    (ZJ_pos _ _ _).le
  exact hlat.trans (mul_le_mul_of_nonneg_right hmono hz)


end StatMech.Ising
