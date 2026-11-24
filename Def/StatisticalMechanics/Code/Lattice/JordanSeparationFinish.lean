module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFinish.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def jsf_PlanarCutCycleDuality (P : PlanarZ2Subgraph) : Prop :=
  Nat.card (regionGraph (imageGraph P)).ConnectedComponent = faceCount P.G


end Lattice
end StatMech
