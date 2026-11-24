module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.KingFacts
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
public import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedBuild
open Finset Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean -/
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


def UnitEdgeOrbitTransport (K : Set (Site 2)) : Prop :=
  ∀ (e : Dart), IsBoundaryDart K e →
    ∀ {u v : Site 2} (_hu : u ∉ K) (_hv : v ∉ K),
      (hypercubicLattice 2).Adj u v →
      OrbitReached K e u → OrbitReached K e v


end Lattice
end StatMech
