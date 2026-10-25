/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenPeel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel
open SimpleGraph Set


namespace StatMech

namespace Lattice

def jvp_VeblenStep (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → jce_ClosedContour (jei_pushGraph P K).edgeSet → K ≠ ⊥ →
    ∃ K' : SimpleGraph P.V, K' ≤ K ∧ jce_ClosedContour (jei_pushGraph P K').edgeSet ∧
      K'.edgeSet.ncard < K.edgeSet.ncard ∧ faceCount K' + 1 = faceCount K


def jvp_RegionStep (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K K' : SimpleGraph P.V), K ≤ P.G → K' ≤ K →
    jce_ClosedContour (jei_pushGraph P K).edgeSet →
    jce_ClosedContour (jei_pushGraph P K').edgeSet →
    K'.edgeSet.ncard < K.edgeSet.ncard → faceCount K' + 1 = faceCount K →
    Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent
      = Nat.card (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent + 1


end Lattice
end StatMech
