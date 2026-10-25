/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Def.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part2
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

@[simp] theorem isingTorusMomentumGridEquiv_apply
    {k : Nat} (p : IsingDyadicTorus d k) :
    (isingTorusMomentumGridEquiv d k p).val =
      isingTorusCenteredMomentumFun p := rfl

theorem isingNormalizedCoordinateDispersion_centered
    {k : Nat} (p : IsingDyadicTorus d k) :
    isingNormalizedCoordinateDispersion
        (isingTorusCenteredMomentumFun p) =
      isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
  rw [isingTorusCharacterDispersion_centered]
  unfold isingNormalizedCoordinateDispersion
  rfl


end StatMech.FrontierA
