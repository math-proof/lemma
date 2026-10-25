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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part6


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialHorizontalEdgeIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat) : Complex :=
  ((mesh : Complex) / 2 * (1 - Complex.I)) * (F i j + F (i + 1) j) / 2


def reflectedRadialVerticalEdgeIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex) (i j : Nat) : Complex :=
  ((mesh : Complex) / 2 * (1 + Complex.I)) * (F i j + F i (j + 1)) / 2

end
end StatMech.Universality
