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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part7


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialDiscretePrimitive
    (H V : Nat -> Nat -> Complex) (i0 j0 a b : Nat) : Complex :=
  (∑ x ∈ Finset.range a, H (i0 + x) j0) +
    ∑ y ∈ Finset.range b, V (i0 + a) (j0 + y)


end
end StatMech.Universality
