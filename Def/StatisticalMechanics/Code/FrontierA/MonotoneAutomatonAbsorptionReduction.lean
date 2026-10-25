/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part4
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def pairDisjointInfiniteHighAt (x : Site d) : Set (PairSiteConfig d) :=
  {omega | (pairHighCluster omega x).Infinite ∧
    ¬(pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty}

end StatMech.FrontierA
