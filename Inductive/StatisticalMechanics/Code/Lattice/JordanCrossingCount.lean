/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
public import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount
open SimpleGraph Set


namespace StatMech

namespace Lattice

public inductive jcx_IsEvenPeelable {V : Type*} : SimpleGraph V → Prop where
  | bot : jcx_IsEvenPeelable (⊥ : SimpleGraph V)
  | cycle {K : SimpleGraph V} (hev : jcx_IsEven K) {v : V} (p : K.Walk v v) (hp : p.IsCycle)
      (hiso : ∀ u ∈ p.support, u ≠ v → ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w)
      (hrec : jcx_IsEvenPeelable (K.deleteEdges p.toSubgraph.edgeSet)) : jcx_IsEvenPeelable K


end Lattice
end StatMech
