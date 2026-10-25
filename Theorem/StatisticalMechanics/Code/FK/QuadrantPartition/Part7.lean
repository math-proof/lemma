/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

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


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section BoxGeom

theorem qp_block_fkZ (d K : ℕ) (s : Fin d → Bool) (p q : ℝ) :
    fkZ (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p q = fkZ (boxGraph d K) p q := by
  have key := agl_left_block_fkZ_eq (2 * K + 1) K (fun x => qp_boxTag d K x = some s)
    (qp_vshift d K s) (qp_quadφ d K s)
    (by intro y
        show (((qp_quadφ d K s y).1 : boxVerts d (2 * K + 1)) : Site d) = (y : Site d) + qp_vshift d K s
        funext i; rfl) p q
  convert key using 2


end BoxGeom
end FK
end StatMech
