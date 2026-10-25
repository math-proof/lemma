/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part3
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWireConfig_setClosed
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : Sym2 (fkSquareBoxPlanar n).V)
    (he : FKIsingSquareSwitchableEdge n e) :
    fkIsingSquareWireConfig n (setClosed e omega) =
      setClosed e (fkIsingSquareWireConfig n omega) := by
  change ¬ fkIsingSquareIsWiredArcEdge n e at he
  funext f
  by_cases hf : f = e
  · subst f
    simp [fkIsingSquareWireConfig, FKIsingSquareSwitchableEdge,
      setClosed, he]
  · by_cases hw : fkIsingSquareIsWiredArcEdge n f
    · simp [fkIsingSquareWireConfig, setClosed, hw, hf]
    · simp [fkIsingSquareWireConfig, setClosed, hw, hf]

theorem fkIsingSquareWireConfig_setOpen
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : Sym2 (fkSquareBoxPlanar n).V)
    (he : FKIsingSquareSwitchableEdge n e) :
    fkIsingSquareWireConfig n (setOpen e omega) =
      setOpen e (fkIsingSquareWireConfig n omega) := by
  change ¬ fkIsingSquareIsWiredArcEdge n e at he
  funext f
  by_cases hf : f = e
  · subst f
    simp [fkIsingSquareWireConfig, FKIsingSquareSwitchableEdge,
      setOpen, he]
  · by_cases hw : fkIsingSquareIsWiredArcEdge n f
    · simp [fkIsingSquareWireConfig, setOpen, hw, hf]
    · simp [fkIsingSquareWireConfig, setOpen, hw, hf]


end
end StatMech.Universality
