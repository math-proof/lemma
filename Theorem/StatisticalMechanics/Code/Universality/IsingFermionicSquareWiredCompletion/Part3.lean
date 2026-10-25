/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareDirectionDart_endpoint_congr (n : Nat)
    {u v : (fkSquareBoxPlanar n).V} (h : u = v)
    (d : FKIsingSquareDirection)
    (hu : fkIsingSquareDirectionAvailable n u d)
    (hv : fkIsingSquareDirectionAvailable n v d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDirectionDart n u d hu turn =
      fkIsingSquareDirectionDart n v d hv turn := by
  subst v
  rfl

end
end StatMech.Universality
