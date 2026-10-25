/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part6


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

inductive FKIsingSquareWiredCarrier (n : Nat)
  | dart : FKIsingMedialDart (fkSquareBoxPlanar n) →
      FKIsingSquareWiredCarrier n
  | bond : FKIsingMedialDart (fkSquareBoxPlanar n) →
      FKIsingSquareWiredCarrier n
  | source : FKIsingSquareWiredCarrier n
  | terminal : FKIsingSquareWiredCarrier n
deriving DecidableEq, Fintype

end
end StatMech.Universality
