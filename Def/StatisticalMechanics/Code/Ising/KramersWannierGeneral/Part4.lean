/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section K4Recovery

noncomputable def k4EdgeCrossing : EdgeCrossing (K4) (K4) where
  ψ := k4CompEquiv
  edge_mem := by
    intro e he
    rw [mem_K4_edgeFinset_iff] at he ⊢
    rw [k4CompEquiv_apply]
    exact k4Comp_not_diag e he
  cut_to_even := by
    intro δ hδ
    rw [cutSpace_eq_cutSpaceB] at hδ
    have := k4Comp_cut_to_even δ hδ
    simpa only [k4CompEquiv_apply] using this
  even_to_cut := by
    intro F hF
    rw [show evenSubgraphs (K4) = evenSubgraphsB (K4) from rfl] at hF
    rw [cutSpace_eq_cutSpaceB]
    have := k4Comp_even_to_cut F hF
    simpa only [k4CompEquiv_symm_apply] using this


end K4Recovery
end Ising
end StatMech
