/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part2
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredArcPathGraph (n : Nat) :
    SimpleGraph (fkSquareBoxPlanar n).V where
  Adj x y := (fkSquareBoxPlanar n).G.Adj x y ∧
    fkIsingSquareWiredArc n x ∧ fkIsingSquareWiredArc n y
  symm := by
    constructor
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := ⟨fun _ h => (fkSquareBoxPlanar n).G.irrefl h.1⟩

end
end StatMech.Universality
