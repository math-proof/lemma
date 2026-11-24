module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
public import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedBuild.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
public import Theorem.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitSeparatesProof
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


def OrbitWindsBdEdge (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) :
    Prop :=
  bdEdge (osp_windingRegion K hK e he) s(e.tail, e.head)


def OrbitFillsWinding (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) :
    Prop :=
  ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
    bdEdge (osp_windingRegion K hK e he) s(x, y) → IsOrbitEdge K e x y


end Lattice
end StatMech
