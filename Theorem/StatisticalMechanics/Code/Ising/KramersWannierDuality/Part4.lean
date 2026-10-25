/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Instance.StatisticalMechanics.Code.Ising.KramersWannierDuality
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section K4

theorem K4_preconnected : (K4).Preconnected := by
  intro x y
  by_cases h : x = y
  · subst h; exact SimpleGraph.Reachable.refl x
  · exact SimpleGraph.Adj.reachable (by simp [K4, h])

set_option maxHeartbeats 2000000 in


theorem k4_cutSpace_evenSubgraph_hist :
    Multiset.map (fun S => S.card) (cutSpaceB (K4)).val
      = Multiset.map (fun S => S.card) (evenSubgraphsB (K4)).val := by
  decide


theorem k4_cutEvenSubgraphMatching (t : ℝ) :
    CutEvenSubgraphMatching (K4) (K4) t 2 := by
  apply cutEvenSubgraphMatching_of_hist (K4) (K4) K4_preconnected t
  rw [cutSpace_eq_cutSpaceB]
  have heq : evenSubgraphs (K4) = evenSubgraphsB (K4) := rfl
  rw [heq]
  exact k4_cutSpace_evenSubgraph_hist


theorem isingZ_self_dual_K4 (β βstar : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    isingZ (K4) βstar 0
      = ((2 : ℝ) ^ Fintype.card (Fin 4) * (Real.cosh βstar) ^ (K4).edgeFinset.card
        / (Real.exp (β * (K4).edgeFinset.card) * 2)) * isingZ (K4) β 0 :=
  isingZ_self_dual_of_cutMatching (K4) (K4) β βstar 2 (by norm_num) htemp
    (k4_cutEvenSubgraphMatching (Real.exp (-2 * β)))

end K4
end Ising
end StatMech
