/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingOpenChainInteraction (L : Nat)
    (sigma : QuantumIsingChainConfig (L + 1)) : Real :=
  ∑ i : Fin L,
    quantumIsingSpinSign (sigma i.castSucc) *
      quantumIsingSpinSign (sigma i.succ)


def quantumIsingLeftBlock {A B : Nat} (sigma : QuantumIsingChainConfig (A + B)) :
    QuantumIsingChainConfig A :=
  fun i => sigma (Fin.castAdd B i)


def quantumIsingRightBlock {A B : Nat} (sigma : QuantumIsingChainConfig (A + B)) :
    QuantumIsingChainConfig B :=
  fun i => sigma (Fin.natAdd A i)

def quantumIsingLeftSpatialBlock (L M : Nat)
    (sigma : QuantumIsingChainConfig (L + M + 2)) :
    QuantumIsingChainConfig (L + 1) :=
  fun i => sigma ⟨i.val, by omega⟩

def quantumIsingRightSpatialBlock (L M : Nat)
    (sigma : QuantumIsingChainConfig (L + M + 2)) :
    QuantumIsingChainConfig (M + 1) :=
  fun i => sigma ⟨L + 1 + i.val, by omega⟩

def quantumIsingSpatialSumEquiv (L M : Nat) :
    Fin (L + 1) ⊕ Fin (M + 1) ≃ Fin (L + M + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

def quantumIsingSpatialJoin (L M : Nat)
    (sigma : QuantumIsingChainConfig (L + 1))
    (tau : QuantumIsingChainConfig (M + 1)) :
    QuantumIsingChainConfig (L + M + 2) :=
  fun i => (quantumIsingSpatialSumEquiv L M).symm i |>.elim sigma tau

end StatMech.FrontierA
