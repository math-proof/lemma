/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteTargetTransport
open Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def pairLowInfiniteVertices (omega : PairSiteConfig d) : Set (Site d) :=
  {x | (cluster d (siteToBond (pairSiteLeft omega)) x).Infinite}


def pairHighCluster (omega : PairSiteConfig d) (x : Site d) : Set (Site d) :=
  cluster d (siteToBond (pairSiteRight omega)) x


def pairNearestHighSet (omega : PairSiteConfig d) (x : Site d) : Set (Site d) :=
  nearestSourceSet (pairHighCluster omega x) (pairLowInfiniteVertices omega)


noncomputable def pairNearestHighFinset (omega : PairSiteConfig d) (x : Site d) :
    Finset (Site d) :=
  nearestSourceFinset (pairHighCluster omega x) (pairLowInfiniteVertices omega)


end StatMech.FrontierA
