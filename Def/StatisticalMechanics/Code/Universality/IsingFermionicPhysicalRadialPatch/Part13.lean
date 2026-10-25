/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part12


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchInteriorEvenRegion
    (n m : Nat) (hm : m ≤ n) (x : (fkSquareBoxPlanar n).V) : Prop :=
  ∃ i j : Fin m, 0 < i.1 ∧ i.1 + 1 < m ∧
    0 < j.1 ∧ j.1 + 1 < m ∧ Even (i.1 + j.1) ∧
      x = fkIsingSquareRadialPatchVertex n m hm i j


end
end StatMech.Universality
