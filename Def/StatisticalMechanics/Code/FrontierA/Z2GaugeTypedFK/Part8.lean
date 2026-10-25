/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part6
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def typedOpenGraph (ends : P -> V × V) (omega : P -> Bool) :
    SimpleGraph V where
  Adj x y := exists p : P, omega p = true ∧
    ((x = (ends p).1 ∧ y = (ends p).2) ∨
      (x = (ends p).2 ∧ y = (ends p).1)) ∧ x ≠ y
  symm := by
    constructor
    rintro x y ⟨p, hp, hxy, hne⟩
    refine ⟨p, hp, ?_, hne.symm⟩
    rcases hxy with hxy | hxy
    · exact Or.inr ⟨hxy.2, hxy.1⟩
    · exact Or.inl ⟨hxy.2, hxy.1⟩
  loopless := ⟨fun x hx => by
    obtain ⟨p, hp, hxy, hne⟩ := hx
    exact hne rfl⟩

end
end StatMech.FrontierA
