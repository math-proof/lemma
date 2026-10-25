/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fkc_rqbdd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


section WeightBound

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkc_fkWeight_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q)
    (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q ω ≤ q ^ Fintype.card V := by
  unfold fkWeight
  have hep : edgeProduct G p ω ≤ 1 := by
    unfold edgeProduct
    apply Finset.prod_le_one
    · intro e _; split <;> [exact hp.le; linarith]
    · intro e _; split <;> [exact hp1.le; linarith]
  have hqk : q ^ numClusters G ω ≤ q ^ Fintype.card V :=
    pow_le_pow_right₀ hq1 (ecz_numClusters_le G ω)
  calc edgeProduct G p ω * q ^ numClusters G ω
      ≤ 1 * q ^ Fintype.card V := by
        exact mul_le_mul hep hqk (by positivity) (by positivity)
    _ = q ^ Fintype.card V := by ring


theorem fkc_fkZEdge_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    ecz_fkZEdge G p q ≤ (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
  unfold ecz_fkZEdge
  calc ∑ ω : ecz_ClosedOff G, fkWeight G p q ω.val
      ≤ ∑ ω : ecz_ClosedOff G, q ^ Fintype.card V :=
        Finset.sum_le_sum (fun ω _ => fkc_fkWeight_le G hp hp1 hq1 ω.val)
    _ = (Fintype.card (ecz_ClosedOff G) : ℝ) * q ^ Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
        rw [ecz_closedOff_card G]; push_cast; ring

end WeightBound
end StatMech.Walls
