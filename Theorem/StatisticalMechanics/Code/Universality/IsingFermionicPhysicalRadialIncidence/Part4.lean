/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

@[simp] theorem fkIsingSquareInteriorRadialEndpoint_mk
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareInteriorRadialEndpoint n hn (Quot.mk _ d) =
      fkIsingSquareDartEndpoint n d.1 := rfl

@[simp] theorem fkIsingSquareInteriorRadialFaceKey_mk
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareInteriorRadialFaceKey n hn (Quot.mk _ d) =
      fkIsingSquareWedgeFaceKey n d.1 := rfl

@[simp] theorem fkIsingSquareInteriorRadialIncrement_mk
    (n : Nat) (hn : 0 < n)
    (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareInteriorRadialIncrement n hn (Quot.mk _ d) =
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart d.1) := rfl

theorem fkIsingSquareInteriorRadialIncrement_nonneg
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    0 ≤ fkIsingSquareInteriorRadialIncrement n hn e := by
  induction e using Quot.ind with
  | _ d => exact fkIsingSquareWiredPrimitiveIncrement_nonneg n hn (.dart d.1)

theorem fkIsingSquareInteriorRadialFaceKey_isInterior
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareInteriorFaceKey n
      (fkIsingSquareInteriorRadialFaceKey n hn e) := by
  induction e using Quot.ind with
  | _ d => exact d.2


end
end StatMech.Universality
