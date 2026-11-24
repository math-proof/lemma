module
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part9
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def step3ContactEvent (T : MonotoneAutomaton d) (D : ℕ)
    (p : Site d × Site d) : Set (FieldTriple d) :=
  {q | p.1 ∈ pairLowInfiniteVertices (interpolatedHighPair T q) ∧
    p.2 ∈ pairNearestHighSet (interpolatedHighPair T q) 0 ∧
    l1dist d p.1 p.2 = D}

end StatMech.FrontierA
