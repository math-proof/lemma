/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryOrderFin_bijective (n : Nat) :
    Function.Bijective (fkIsingSquareBoundaryOrderFin n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j h
    apply fkIsingSquareBoundaryOrderKey_injective n
    exact Fin.mk.inj h
  · simp [FKIsingSquareBoundaryIndex]
    have hcard : Fintype.card FKIsingSquareBoundarySide = 4 := by
      decide
    rw [hcard]
    omega


end
end StatMech.Universality
