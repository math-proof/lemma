/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part12
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section BoxNesting

variable {d : ℕ}


section VanHove

variable {d : ℕ}


theorem ecz_cellBlock_fkZEdge (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) (p q : ℝ) :
    ecz_fkZEdge (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)) p q
      = ecz_fkZEdge (boxGraph d m) p q :=
  (ecz_fkZEdge_iso (ecz_cellBlockIso m n c) p q).symm


theorem ecz_cellBlock_edge_card (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) :
    (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)).edgeFinset.card
      = (boxGraph d m).edgeFinset.card :=
  ((ecz_cellBlockIso m n c).card_edgeFinset_eq).symm


theorem ecz_cell_card (m n : ℕ) : Fintype.card (Fin d → Fin (ecz_T m n)) = (ecz_T m n) ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]


end VanHove
end BoxNesting
end FK
end StatMech
