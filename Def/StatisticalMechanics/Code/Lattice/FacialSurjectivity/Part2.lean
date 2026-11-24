module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
public import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.FacialSurjectivity
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def fsv_RegionSingleFace (C : Set (Site 2)) : Prop :=
  ∀ e : Dart, IsBoundaryDart C e →
    {d : Dart | IsBoundaryDart C d} = {d : Dart | SameOrbit C e d}


def fsv_singleOrbitFamily {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Set (Set Dart) :=
  {D | ∃ z : Site 2, z ∉ Vc.support ∧ ∃ e : Dart, IsBoundaryDart (offSupportComponent Vc z) e ∧
    D = {d : Dart | SameOrbit (offSupportComponent Vc z) e d}}


end Lattice
end StatMech
