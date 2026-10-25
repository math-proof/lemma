/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Def.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section Matching

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


theorem dualContourMatching_of_cutMatching (β βstar mult : ℝ)
    (hmult : mult ≠ 0)
    (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : CutEvenSubgraphMatching Gp Gd (Real.exp (-2 * β)) mult) :
    DualContourMatching Gp Gd β βstar
      ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        / (Real.exp (β * Gp.edgeFinset.card) * mult)) := by
  refine ⟨htemp, ?_⟩
  unfold CutEvenSubgraphMatching at hmatch
  rw [isingZ_low_temp_expansion Gp β]
  rw [← htemp] at hmatch ⊢
  set Sd := ∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh βstar) ^ F.card
  have hexp : (0 : ℝ) < Real.exp (β * Gp.edgeFinset.card) := Real.exp_pos _
  rw [hmatch]
  field_simp


theorem isingZ_self_dual_of_cutMatching (β βstar mult : ℝ)
    (hmult : mult ≠ 0)
    (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : CutEvenSubgraphMatching Gp Gd (Real.exp (-2 * β)) mult) :
    isingZ Gd βstar 0
      = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        / (Real.exp (β * Gp.edgeFinset.card) * mult)) * isingZ Gp β 0 :=
  isingZ_self_dual Gp Gd β βstar _
    (dualContourMatching_of_cutMatching Gp Gd β βstar mult hmult htemp hmatch)

end Matching
end Ising
end StatMech
