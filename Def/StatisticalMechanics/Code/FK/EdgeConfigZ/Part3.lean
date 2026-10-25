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
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part2
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


section PartitionPeel

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


noncomputable def ecz_uu {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℝ) : ℝ := -Real.log (ecz_fkZEdge G p q)

end PartitionPeel
end FK
end StatMech
