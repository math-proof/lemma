/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


def pairHasDisjointInfiniteHighCluster : Set (PairSiteConfig d) :=
  {omega | ∃ x : Site d, omega ∈ pairDisjointInfiniteHighAt x}

end StatMech.FrontierA
