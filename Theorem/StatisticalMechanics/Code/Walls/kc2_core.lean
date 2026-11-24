module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
public import Theorem.StatisticalMechanics.Code.Walls.kc2_supportisface
public import Theorem.StatisticalMechanics.Code.Walls.kc2_dartdircases
public import Theorem.StatisticalMechanics.Code.Walls.kc2_rightfaceinK
public import Theorem.StatisticalMechanics.Code.Walls.kc2_downfaceoutK
public import Theorem.StatisticalMechanics.Code.Walls.kc2_leftupfacecell.Part2
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc2_supportOdd_right {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![1, 0]) :
    dartFace e ∈ K :=
  kc2_rightDart_face_mem_K K e he hd


end Walls
end StatMech
