/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part2
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWireConfig_wired
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {e : Sym2 (fkSquareBoxPlanar n).V}
    (he : fkIsingSquareIsWiredArcEdge n e) :
    fkIsingSquareWireConfig n omega e = true := by
  simp [fkIsingSquareWireConfig, he]

theorem fkIsingSquareWireConfig_nonwired
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {e : Sym2 (fkSquareBoxPlanar n).V}
    (he : ¬ fkIsingSquareIsWiredArcEdge n e) :
    fkIsingSquareWireConfig n omega e = omega e := by
  simp [fkIsingSquareWireConfig, he]


end
end StatMech.Universality
