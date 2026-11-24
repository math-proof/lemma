module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
public import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part3
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


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section Peel

variable {T : Type*} [DecidableEq T] (tag : U → T)


noncomputable instance (P : U → Prop) [DecidablePred P] : DecidablePred (qp_straddleP P) :=
  fun _ => Classical.dec _


end Peel
end FK
end StatMech
