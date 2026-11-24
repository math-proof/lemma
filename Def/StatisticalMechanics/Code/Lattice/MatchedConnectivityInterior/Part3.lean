module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def mci_FourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ u v : Site 2, u ∈ Vc.support → v ∈ Vc.support →
    (hypercubicLattice 2).Adj u v → s(u, v) ∈ Vc.edges


end Lattice
end StatMech
