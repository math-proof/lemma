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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part34


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareExteriorCutTurn_forward
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareExteriorCutTurn n hn
      (fkIsingSquareExteriorCutStart n hn)
      (fkIsingSquareExteriorCutEnd n hn) = 8 := by
  simp [fkIsingSquareExteriorCutTurn,
    fkIsingSquareExteriorCutStart, fkIsingSquareExteriorCutEnd,
    fkIsingSquareBondMate_sourceEdge_ne_terminalEdge]

@[simp] theorem fkIsingSquareExteriorCutTurn_reverse
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareExteriorCutTurn n hn
      (fkIsingSquareExteriorCutEnd n hn)
      (fkIsingSquareExteriorCutStart n hn) = -8 := by
  have hne : fkIsingSquareExteriorCutEnd n hn ≠
      fkIsingSquareExteriorCutStart n hn := by
    intro h
    exact fkIsingSquareBondMate_sourceEdge_ne_terminalEdge n hn
      (congrArg Prod.fst h.symm)
  simp [fkIsingSquareExteriorCutTurn, hne]


theorem fkIsingSquareExteriorCutTurn_forward_unique (z : Int)
    (hzmod : z % 8 = 0) (hzlo : 4 < z) (hzhi : z ≤ 12) : z = 8 := by
  omega


theorem fkIsingSquareExteriorCutTurn_reverse_unique (z : Int)
    (hzmod : z % 8 = 0) (hzlo : -12 ≤ z) (hzhi : z < -4) : z = -8 := by
  omega


theorem fkIsingSquareExteriorCut_principal_forward
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareSignedEighthTurn
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutStart n hn)))
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutEnd n hn)) + 4) = 0 := by
  simp [fkIsingSquareSignedEighthTurn]

theorem fkIsingSquareExteriorCut_principal_reverse
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareSignedEighthTurn
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutEnd n hn)))
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutStart n hn)) + 4) = 0 := by
  simp [fkIsingSquareSignedEighthTurn]


end
end StatMech.Universality
