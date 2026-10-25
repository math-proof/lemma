/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part7


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareWiredFullLeftCycle_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredFullLeftCycle n hn) := by
  intro k l hkl
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareWiredFullLeftDart n hn k)
        (fkIsingSquareWiredFullLeftDart n hn l) :=
    Quotient.exact hkl
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hor := fkIsingSquareWiredFullLeftDart_pow_mem n hn k m
  rw [hm] at hor
  rcases hor with h | h
  · have hv := congrArg Subtype.val h
    simp only [fkIsingSquareWiredFullLeftDart,
      FKIsingSquareWiredCarrier.dart.injEq] at hv
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn hv
    cases hi
    rfl
  · have hv := congrArg Subtype.val h
    simp [fkIsingSquareWiredFullLeftDart,
      fkIsingSquareWiredFullLeftBond] at hv

end
end StatMech.Universality
