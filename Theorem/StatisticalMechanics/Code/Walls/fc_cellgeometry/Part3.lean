/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean -/

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
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Def.StatisticalMechanics.Code.Walls.fc_cellgeometry
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


section VanHove

variable {d : ℕ}


theorem fc_cellBlockIso_apply (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) (y : boxVerts d m) :
    (((fc_cellBlockIso m n c y : {x : boxVerts d n // fc_vanHoveTag m n x = some c}) :
        boxVerts d n) : Site d)
      = fun i => (y : Site d) i + fc_center m n c i :=
  rfl


theorem fc_cellBlock_fkZEdge (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) (p q : ℝ) :
    ecz_fkZEdge (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) p q
      = ecz_fkZEdge (boxGraph d m) p q :=
  ecz_cellBlock_fkZEdge m n c p q


theorem fc_cellBlock_fkZEdge_via_iso_load_bearing (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n))
    (p q : ℝ) :
    ecz_fkZEdge (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) p q
      = ecz_fkZEdge (boxGraph d m) p q :=
  (fc_fkZEdge_iso (fc_cellBlockIso m n c) p q).symm


theorem fc_cellBlock_edge_card (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) :
    (qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)).edgeFinset.card
      = (boxGraph d m).edgeFinset.card :=
  ecz_cellBlock_edge_card m n c


theorem fc_cell_card (m n : ℕ) :
    Fintype.card (Fin d → Fin (fc_Tcg m n)) = (fc_Tcg m n) ^ d :=
  ecz_cell_card m n


end VanHove
end StatMech.Walls
