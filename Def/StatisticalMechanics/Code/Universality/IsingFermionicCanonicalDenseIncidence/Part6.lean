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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part5
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

noncomputable def fkIsingDenseRationalIncidence
    (q : Rat × Rat) (k : Nat) :
    FKIsingSquareInteriorRadialIncidence
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k) := by
  let x := fkIsingDenseRationalPrimalX q k
  let y := fkIsingDenseRationalPrimalY q k
  if h : -(fkIsingExpandingSquareSide k : Int) ≤ x ∧
      x < fkIsingExpandingSquareSide k ∧
      -(fkIsingExpandingSquareSide k : Int) ≤ y ∧
      y < fkIsingExpandingSquareSide k then
    exact fkIsingSquareInteriorRadialIncidenceOfInt
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      x y h
  else
    exact fkIsingSquareInteriorRadialIncidenceOfInt
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      0 0 (by
        have hn := fkIsingExpandingSquareSide_pos k
        constructor
        · omega
        constructor
        · exact_mod_cast hn
        constructor
        · omega
        · exact_mod_cast hn)


end
end StatMech.Universality
