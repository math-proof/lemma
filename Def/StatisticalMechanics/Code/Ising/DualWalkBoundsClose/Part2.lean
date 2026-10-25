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
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section LatticeRealisation

open StatMech.Lattice


def DualWalkLeftRegionMatch {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    {w : Site 2} (W : Gd.Walk w w) : Prop :=
  ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image crossEdge.symm ↔ bdEdge (jec_leftRegion Vc) s(u, v))


end LatticeRealisation
end Ising
end StatMech
