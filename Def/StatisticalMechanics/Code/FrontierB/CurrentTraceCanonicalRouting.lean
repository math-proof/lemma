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
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCanonicalRouting
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation

open Percolation.DisjointPaths

variable {d : ℕ}


def OriginNeighborsCutConnected
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ a b : Site d, (hypercubicLattice d).Adj 0 a →
    (hypercubicLattice d).Adj 0 b → Connected d (removeSite 0 ω) a b


end StatMech.FrontierB
