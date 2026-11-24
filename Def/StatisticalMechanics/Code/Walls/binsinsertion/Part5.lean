module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.bcl2close.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
public import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
public import Theorem.StatisticalMechanics.Code.Walls.binsinsertion.Part5
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bins_outSide (n : ℕ) (u : Site 2) : Fin 4 :=
  if u 0 = (n : ℤ) + 1 then 0
  else if u 0 = -((n : ℤ) + 1) then 1
  else if u 1 = (n : ℤ) + 1 then 2
  else 3


end StatMech.Walls
