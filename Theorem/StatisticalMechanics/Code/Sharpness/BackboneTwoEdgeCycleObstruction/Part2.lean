/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open FluxEdgeCopy

theorem headEdge_ne_suffixEdge : headEdge ≠ suffixEdge := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((1 : Fin 6), 2))
    (congrArg Subtype.val h)

theorem headEdge_ne_cycleEdge₀ : headEdge ≠ cycleEdge₀ := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((3 : Fin 6), 4))
    (congrArg Subtype.val h)

theorem headEdge_ne_cycleEdge₁ : headEdge ≠ cycleEdge₁ := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((4 : Fin 6), 5))
    (congrArg Subtype.val h)

theorem headEdge_ne_cycleEdge₂ : headEdge ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_cycleEdge₀ : suffixEdge ≠ cycleEdge₀ := by
  intro h
  exact (by decide : s((1 : Fin 6), 2) ≠ s((3 : Fin 6), 4))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_cycleEdge₁ : suffixEdge ≠ cycleEdge₁ := by
  intro h
  exact (by decide : s((1 : Fin 6), 2) ≠ s((4 : Fin 6), 5))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_cycleEdge₂ : suffixEdge ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((1 : Fin 6), 2) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem cycleEdge₀_ne_cycleEdge₁ : cycleEdge₀ ≠ cycleEdge₁ := by
  intro h
  exact (by decide : s((3 : Fin 6), 4) ≠ s((4 : Fin 6), 5))
    (congrArg Subtype.val h)

theorem cycleEdge₀_ne_cycleEdge₂ : cycleEdge₀ ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((3 : Fin 6), 4) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem cycleEdge₁_ne_cycleEdge₂ : cycleEdge₁ ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((4 : Fin 6), 5) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_headEdge : suffixEdge ≠ headEdge :=
  headEdge_ne_suffixEdge.symm

theorem cycleEdge₀_ne_headEdge : cycleEdge₀ ≠ headEdge :=
  headEdge_ne_cycleEdge₀.symm

theorem cycleEdge₁_ne_headEdge : cycleEdge₁ ≠ headEdge :=
  headEdge_ne_cycleEdge₁.symm

theorem cycleEdge₂_ne_headEdge : cycleEdge₂ ≠ headEdge :=
  headEdge_ne_cycleEdge₂.symm

theorem cycleEdge₀_ne_suffixEdge : cycleEdge₀ ≠ suffixEdge :=
  suffixEdge_ne_cycleEdge₀.symm

theorem cycleEdge₁_ne_suffixEdge : cycleEdge₁ ≠ suffixEdge :=
  suffixEdge_ne_cycleEdge₁.symm

theorem cycleEdge₂_ne_suffixEdge : cycleEdge₂ ≠ suffixEdge :=
  suffixEdge_ne_cycleEdge₂.symm

theorem cycleEdge₁_ne_cycleEdge₀ : cycleEdge₁ ≠ cycleEdge₀ :=
  cycleEdge₀_ne_cycleEdge₁.symm

theorem cycleEdge₂_ne_cycleEdge₀ : cycleEdge₂ ≠ cycleEdge₀ :=
  cycleEdge₀_ne_cycleEdge₂.symm

theorem cycleEdge₂_ne_cycleEdge₁ : cycleEdge₂ ≠ cycleEdge₁ :=
  cycleEdge₁_ne_cycleEdge₂.symm

end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
