/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnChainRefinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Existence of an intermediate subspace whenever the dimension gap is at least $2$, by
adjoining a single vector $v \in B \setminus A$. -/
noncomputable def chainInsertionHyp : ChainInsertionHyp k n where
  fill_gap := fun A B hAB hgap => by

    obtain ⟨v, hv_in_B, hv_not_A⟩ := Set.exists_of_ssubset hAB

    have hv_ne : v ≠ 0 := fun h => hv_not_A (h ▸ Submodule.zero_mem A)

    have hdisjoint : Disjoint A (Submodule.span k {v}) := by
      rw [Submodule.disjoint_span_singleton]; exact fun h => absurd h hv_not_A

    have hfr : Module.finrank k ↥(A ⊔ Submodule.span k {v}) =
        Module.finrank k ↥A + 1 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span k {v})
      rw [hdisjoint.eq_bot, finrank_bot, finrank_span_singleton hv_ne] at h; omega
    exact ⟨A ⊔ Submodule.span k {v},

      lt_of_le_of_ne le_sup_left (fun heq =>
        hv_not_A (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))),

      Submodule.lt_of_le_of_finrank_lt_finrank
        (sup_le hAB.le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_in_B)))
        (hfr ▸ by omega)⟩


end GLnBuilding
