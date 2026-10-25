/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part9


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialRectangleBoundaryIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat) : Complex :=
  (∑ i ∈ Finset.range width,
      reflectedRadialHorizontalEdgeIntegral mesh F (i0 + i) j0) +
    (∑ j ∈ Finset.range height,
      reflectedRadialVerticalEdgeIntegral mesh F (i0 + width) (j0 + j)) -
    (∑ i ∈ Finset.range width,
      reflectedRadialHorizontalEdgeIntegral mesh F (i0 + i) (j0 + height)) -
    (∑ j ∈ Finset.range height,
      reflectedRadialVerticalEdgeIntegral mesh F i0 (j0 + j))


end
end StatMech.Universality
