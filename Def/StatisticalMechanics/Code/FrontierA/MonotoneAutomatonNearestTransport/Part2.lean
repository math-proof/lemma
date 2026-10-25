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
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport
open Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


noncomputable def pairNearestTransport (x y : Site d) (omega : PairSiteConfig d) :
    ℝ≥0∞ :=
  finiteTargetTransport (pairHighCluster omega x)
    (pairNearestHighFinset omega x) x y


end StatMech.FrontierA
