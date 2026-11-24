module
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonPairLaw.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.FiniteTargetTransport
public import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport
open Set
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonNearestTransport.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def pairNearestTransport (x y : Site d) (omega : PairSiteConfig d) :
    ENNReal :=
  finiteTargetTransport (pairHighCluster omega x)
    (pairNearestHighFinset omega x) x y


end StatMech.FrontierA
