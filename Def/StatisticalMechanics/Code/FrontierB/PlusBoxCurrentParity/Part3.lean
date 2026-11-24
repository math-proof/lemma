module
public import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentParity.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
public import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.PlusBoxCurrentParity.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusBoxCurrentParity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.IsingFK

def currentParityAvoidCylinder {E : Type*} (F : Finset E) :
    Set (InfiniteCurrentConfig E) :=
  {m | ∀ e ∈ F, Even (m e)}

end StatMech.FrontierB
