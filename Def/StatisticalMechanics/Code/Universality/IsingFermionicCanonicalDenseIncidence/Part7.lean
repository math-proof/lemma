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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part6
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

noncomputable def fkIsingExpandingSquareDenseIncidenceFamily :
    FKIsingDenseIncidenceFamily
      fkIsingExpandingSquareSide fkIsingExpandingSquareSide_pos
      fkIsingExpandingSquareScale where
  point := fkIsingDenseRationalPoint
  incidence j k :=
    fkIsingDenseRationalIncidence (fkIsingRationalPairEnumeration j) k
  embedding_tendsto j := by
    exact fkIsingDenseRationalIncidence_embedding_tendsto
      (fkIsingRationalPairEnumeration j)
  dense_range := fkIsingDenseRationalPoint_denseRange


def FKIsingDenseRationalInterior (q : Rat × Rat) (k : Nat) : Prop :=
  -(fkIsingExpandingSquareSide k : Int) ≤
      fkIsingDenseRationalPrimalX q k ∧
    fkIsingDenseRationalPrimalX q k < fkIsingExpandingSquareSide k ∧
  -(fkIsingExpandingSquareSide k : Int) ≤
      fkIsingDenseRationalPrimalY q k ∧
    fkIsingDenseRationalPrimalY q k < fkIsingExpandingSquareSide k


noncomputable def fkIsingDenseRationalPathX (q : Rat × Rat) (k : Nat) : Int := by
  classical
  exact if FKIsingDenseRationalInterior q k then
      fkIsingDenseRationalPrimalX q k else 0

noncomputable def fkIsingDenseRationalPathY (q : Rat × Rat) (k : Nat) : Int := by
  classical
  exact if FKIsingDenseRationalInterior q k then
      fkIsingDenseRationalPrimalY q k else 0


def fkIsingDenseRationalPathSteps (q : Rat × Rat) (k : Nat) : Nat :=
  (fkIsingDenseRationalPathX q k).natAbs +
    (fkIsingDenseRationalPathY q k).natAbs


end
end StatMech.Universality
