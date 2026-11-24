module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def jfc_whb_outerRegion (P : PlanarZ2Subgraph) :
    (whb_faceRegion (imageGraph P)).ConnectedComponent :=
  (whb_faceRegion (imageGraph P)).connectedComponentMk (beacon 2 (outerBoxRadius P + 1))


end Lattice
end StatMech
