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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part15


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialAxisSnapI (n : Nat) (mesh : Real) (z : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊z.im / mesh⌋)

def reflectedRadialAxisSnapJ (n : Nat) (mesh : Real) (z : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋)


def reflectedRadialAxisSnapBaseI
    (n : Nat) (mesh : Real) (z w : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ - ⌊w.im / mesh⌋)

def reflectedRadialAxisSnapBaseJ
    (n : Nat) (mesh : Real) (z : Complex) : Nat :=
  Int.toNat ((n : Int) + ⌊z.re / mesh - 1 / 2⌋ + ⌊z.im / mesh⌋)


end
end StatMech.Universality
