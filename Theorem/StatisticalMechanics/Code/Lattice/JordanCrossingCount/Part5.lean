/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcx_cross_deg2 : jcx_cross_G.neighborSet 2 = {1, 3, 4, 6} := by
  ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]


theorem jcx_cross_not_isCycles : ¬ jcx_cross_G.IsCycles := by
  intro hcyc
  have hv : (jcx_cross_G.neighborSet 2).Nonempty :=
    ⟨1, by rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; decide⟩
  have h2 := hcyc hv
  rw [jcx_cross_deg2, show ({1, 3, 4, 6} : Set (Fin 7)).ncard = 4 by
    rw [Set.ncard_eq_toFinset_card']; decide] at h2
  exact absurd h2 (by decide)


theorem jcx_cross_isEven : jcx_IsEven jcx_cross_G := by
  intro v
  rw [Nat.card_coe_set_eq]
  have key : (jcx_cross_G.neighborSet v).ncard = 2 ∨ (jcx_cross_G.neighborSet v).ncard = 4 := by
    fin_cases v
    · left; rw [show jcx_cross_G.neighborSet ⟨0, by omega⟩ = {1, 3} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨1, by omega⟩ = {0, 2} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · right; rw [show jcx_cross_G.neighborSet ⟨2, by omega⟩ = {1, 3, 4, 6} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      rw [Set.ncard_eq_toFinset_card']; decide
    · left; rw [show jcx_cross_G.neighborSet ⟨3, by omega⟩ = {2, 0} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨4, by omega⟩ = {2, 5} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨5, by omega⟩ = {4, 6} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
    · left; rw [show jcx_cross_G.neighborSet ⟨6, by omega⟩ = {5, 2} by
        ext j; rw [SimpleGraph.mem_neighborSet, jcx_cross_G_adj]; fin_cases j <;> simp [jcx_cross_rel]]
      exact Set.ncard_pair (by decide)
  rcases key with h | h <;> rw [h] <;> decide


end Lattice
end StatMech
