/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part4
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

def fkIsingDenseRationalPrimalX (q : Rat × Rat) (k : Nat) : Int :=
  ⌊(((q.1 : Real) + (q.2 : Real)) / 2) * (k + 1 : Real)⌋

def fkIsingDenseRationalPrimalY (q : Rat × Rat) (k : Nat) : Int :=
  ⌊(((q.1 : Real) - (q.2 : Real)) / 2) * (k + 1 : Real)⌋


end
end StatMech.Universality
