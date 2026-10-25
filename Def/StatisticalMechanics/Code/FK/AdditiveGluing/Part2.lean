/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

section Partition

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]
  (P : U → Prop) [DecidablePred P]


noncomputable def agl_iso : K₀ ≃g agl_glueGraph K₀ P where
  toEquiv := (agl_sumEquiv P).symm
  map_rel_iff' := by
    intro a b
    rw [agl_glueGraph_adj]
    simp only [Equiv.apply_symm_apply]


noncomputable def agl_interfaceCard : ℕ :=
  (fis_interface (agl_left K₀ P) (agl_right K₀ P) (agl_glueGraph K₀ P)).card


end Partition
end FK
end StatMech
