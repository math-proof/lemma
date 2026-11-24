module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
public import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
public import Theorem.StatisticalMechanics.Code.FK.DensityBounds
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
public import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
public import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
public import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
public import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
public import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part2
open Set Filter Topology
open scoped BigOperators
open StatMech.FK
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


open StatMech.Lattice

variable {d : ℕ}


def fpe2_GenuineFreeCollapse (d N : ℕ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop
      (𝓝 (freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))


def fpe2_GenuineWiredCollapse (d N : ℕ) : Prop :=
  ∀ e' ∈ (boxGraph d N).edgeFinset, ∀ t : ℝ,
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop
      (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)))


end FK
end StatMech
