/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SignOrthantTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.SignOrthantTiling.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
open SimpleGraph

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

open ConfigSpace StatMech.Lattice


def sot_OrthantCrossSplit (d : ℕ) (t : ℝ) (C : ℝ) (j : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
    (K : SimpleGraph (boxVerts d (2 ^ j) ⊕ W)) (_ : DecidableRel K.Adj),
    fis_CrossInterface (boxGraph d (2 ^ j)) H K
    ∧ (Nonempty (boxGraph d (2 ^ (j + 1)) ≃g K))
    ∧ ((fkZ (boxGraph d (2 ^ j)) (fsc_logistic t) 2) ^ (2 ^ d - 1)
        ≤ fkZ H (fsc_logistic t) 2)
    ∧ ((fis_interface (boxGraph d (2 ^ j)) H K).card : ℝ)
        ≤ C * (4 * (2 : ℝ) ^ j + 1) ^ (d - 1)
    ∧ |(2 : ℝ) ^ d * bxt_E d (2 ^ j) - bxt_E d (2 ^ (j + 1))|
        ≤ ((fis_interface (boxGraph d (2 ^ j)) H K).card : ℝ)


end FK
end StatMech
