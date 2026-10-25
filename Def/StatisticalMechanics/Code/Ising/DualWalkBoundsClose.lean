/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section LatticeRealisation

open StatMech.Lattice


def LatticeDualWalkHasBdEdgeRegion (Gd : SimpleGraph (Site 2)) [DecidableRel Gd.Adj] : Prop :=
  ∀ {w : Site 2} (W : Gd.Walk w w), ∃ S : Set (Site 2),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge S s(u, v))


end LatticeRealisation
end Ising
end StatMech
