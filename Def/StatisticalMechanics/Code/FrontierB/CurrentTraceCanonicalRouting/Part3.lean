/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceClusterUniqueness
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCanonicalRouting.Part3
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation

open Percolation.DisjointPaths

variable {d : ℕ}


def hubTripleEdges (z a₁ a₂ a₃ : Site d) :
    Finset (Sym2 (Site d)) :=
  {s(z, a₁), s(z, a₂), s(z, a₃)}


end StatMech.FrontierB
