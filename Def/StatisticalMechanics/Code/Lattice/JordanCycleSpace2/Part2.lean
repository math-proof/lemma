module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace2.Part2
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace2.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def jcx_EvenPeel (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → jce_ClosedContour (jei_pushGraph P K).edgeSet →
    K ≠ ⊥ →
    ∃ K' : SimpleGraph P.V, K' ≤ P.G ∧ jce_ClosedContour (jei_pushGraph P K').edgeSet ∧
      K'.edgeSet.ncard < K.edgeSet.ncard ∧
      faceCount K' + 1 = faceCount K ∧
      Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent
        = Nat.card (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent + 1


end Lattice
end StatMech
