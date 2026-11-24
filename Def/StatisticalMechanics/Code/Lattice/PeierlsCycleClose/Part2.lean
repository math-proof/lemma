module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
public import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
public import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossArcThickClose.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WindingPinchClose
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsCycleClose.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def pcy_CrossArcThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  Vc.IsCycle → cat_CrossArcThick Vc seed


end Lattice
end StatMech
