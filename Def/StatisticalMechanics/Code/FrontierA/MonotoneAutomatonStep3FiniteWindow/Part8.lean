/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part8
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def pairStep3DistanceAt (root : Site d) (D : ℕ) : Set (PairSiteConfig d) :=
  pairStep3CoreAt root ∩
    {omega | ∀ y ∈ pairHighCluster omega root,
      ∀ x ∈ pairLowInfiniteVertices omega, D ≤ l1dist d y x} ∩
    {omega | ∃ y ∈ pairHighCluster omega root,
      ∃ x ∈ pairLowInfiniteVertices omega, l1dist d y x = D}

end StatMech.FrontierA
