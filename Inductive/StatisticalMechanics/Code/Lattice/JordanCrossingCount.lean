/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount
open SimpleGraph Set


namespace StatMech

namespace Lattice

inductive jcx_IsEvenPeelable {V : Type*} : SimpleGraph V → Prop where
  | bot : jcx_IsEvenPeelable (⊥ : SimpleGraph V)
  | cycle {K : SimpleGraph V} (hev : jcx_IsEven K) {v : V} (p : K.Walk v v) (hp : p.IsCycle)
      (hiso : ∀ u ∈ p.support, u ≠ v → ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w)
      (hrec : jcx_IsEvenPeelable (K.deleteEdges p.toSubgraph.edgeSet)) : jcx_IsEvenPeelable K


end Lattice
end StatMech
