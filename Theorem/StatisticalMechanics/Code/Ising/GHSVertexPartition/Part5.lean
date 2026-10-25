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
import Def.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part4
open Finset Classical

set_option maxHeartbeats 1600000


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls

variable {W : Type*} [Fintype W] [DecidableEq W]


@[simp] theorem ghsvp_inactiveConfig_card (S : Finset W) :
    Fintype.card (({v : W // v ∉ S}) -> Bool) =
      2 ^ (Fintype.card W - S.card) := by
  rw [Fintype.card_fun, Fintype.card_subtype_compl]
  simp


theorem ghsvp_vertexZ_eq_inactiveCard_mul_activeZ
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (S : Finset W) :
    ghsvp_vertexZ E J S =
      Fintype.card (({v : W // v ∉ S}) -> Bool) * ghsvp_activeZ E J S := by
  unfold ghsvp_vertexZ ZJ ghsvp_activeZ
  rw [← Equiv.sum_comp (ghsvp_splitConfig S).symm
    (fun s => wJ (ghsvp_vertexEdges E S) J (fun _ => 0) s)]
  simp only [ghsvp_splitConfig, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type]
  simp_rw [ghsvp_wJ_mergeConfig_independent E J S _ _ (fun _ => false)]
  simp [Finset.mul_sum]


end StatMech.Ising
