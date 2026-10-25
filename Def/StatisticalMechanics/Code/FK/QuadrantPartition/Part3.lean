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
import Instance.StatisticalMechanics.Code.FK.QuadrantPartition
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


section Peel

variable {T : Type*} [DecidableEq T] (tag : U → T)


def qp_straddleP (P : U → Prop) [DecidablePred P] : Sym2 U → Prop :=
  Sym2.lift ⟨fun a b => (P a ∧ ¬ P b) ∨ (¬ P a ∧ P b),
    by intro a b; by_cases ha : P a <;> by_cases hb : P b <;> simp [ha, hb]⟩

end Peel
end FK
end StatMech
