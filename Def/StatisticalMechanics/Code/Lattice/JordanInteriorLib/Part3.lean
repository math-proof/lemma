module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
public import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
public import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part3
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def jil_interiorStepGraph {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    SimpleGraph (jil_offSupportInterior Vc) :=
  (hypercubicLattice 2).induce (jil_offSupportInterior Vc)


end Lattice
end StatMech
