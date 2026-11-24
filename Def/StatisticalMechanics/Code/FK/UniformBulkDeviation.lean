module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.SpatialCollapse
public import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
public import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
public import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
public import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
open MeasureTheory Set Filter Topology Real
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}


def ubd_FreeGrowingBoxCollapse (N : ℕ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))


end FK
end StatMech
