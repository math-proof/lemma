/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part7
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable def whc_faithfulRegionCount (P : PlanarZ2Subgraph) : ℕ :=
  Nat.card {c : (whb_faceRegion (imageGraph P)).ConnectedComponent // c.supp.Finite}


def whc_FaithfulDiscreteJordan (P : PlanarZ2Subgraph) : Prop :=
  Nonempty ({c : (whb_faceRegion (imageGraph P)).ConnectedComponent // c.supp.Finite} ≃
    Fin (nullity P.G))


end Lattice
end StatMech
