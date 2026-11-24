module
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestMeasurable.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion
open MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestConclusion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def pairHasFiniteNearestHighCluster : Set (PairSiteConfig d) :=
  {omega | (pairLowInfiniteVertices omega).Nonempty ∧
    ∃ x : Site d, (pairHighCluster omega x).Infinite ∧
      (pairNearestHighSet omega x).Finite}


end StatMech.FrontierA
