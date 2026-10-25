/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanGeneralCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount
open SimpleGraph Set


namespace StatMech

namespace Lattice

inductive jgc_IsCactus {V : Type*} : SimpleGraph V → Prop where
  | bot : jgc_IsCactus (⊥ : SimpleGraph V)
  | leaf {K : SimpleGraph V} {x z : V} (hadj : K.Adj x z) (huniq : ∀ w, K.Adj x w → w = z)
      (hrec : jgc_IsCactus (K.deleteEdges {s(x, z)})) : jgc_IsCactus K
  | cycle {K : SimpleGraph V} (hcyc : K.IsCycles) {v : V} (p : K.Walk v v) (hp : p.IsCycle)
      (hrec : jgc_IsCactus (K.deleteEdges p.toSubgraph.edgeSet)) : jgc_IsCactus K


end Lattice
end StatMech
