/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part3
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.flexible false
set_option linter.style.multiGoal false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


section RootedBlocks

variable {P₁ P₂ V₁ V₂ : Type*}
  [Fintype P₁] [DecidableEq P₁] [Fintype P₂] [DecidableEq P₂]
  [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]


def rootedSumInl : Option V₁ → Option (V₁ ⊕ V₂)
  | none => none
  | some v => some (.inl v)


def rootedSumInr : Option V₂ → Option (V₁ ⊕ V₂)
  | none => none
  | some v => some (.inr v)


def multibondRootedSumEnds
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂) :
    P₁ ⊕ P₂ → Option (V₁ ⊕ V₂) × Option (V₁ ⊕ V₂)
  | .inl p => (rootedSumInl (ends₁ p).1, rootedSumInl (ends₁ p).2)
  | .inr p => (rootedSumInr (ends₂ p).1, rootedSumInr (ends₂ p).2)


def rootedSumAnchoredEquiv :
    AnchoredConfig (Option (V₁ ⊕ V₂)) none ≃
      AnchoredConfig (Option V₁) none × AnchoredConfig (Option V₂) none where
  toFun s :=
    (⟨fun q => s.1 (rootedSumInl q), by simpa [rootedSumInl] using s.2⟩,
      ⟨fun q => s.1 (rootedSumInr q), by simpa [rootedSumInr] using s.2⟩)
  invFun st := ⟨fun q => match q with
    | none => false
    | some (.inl v) => st.1.1 (some v)
    | some (.inr v) => st.2.1 (some v), rfl⟩
  left_inv s := by
    apply Subtype.ext
    funext q
    cases q with
    | none => simpa using s.2.symm
    | some q => cases q <;> rfl
  right_inv st := by
    rcases st with ⟨s₁, s₂⟩
    apply Prod.ext
    · apply Subtype.ext
      funext q
      cases q with
      | none => exact s₁.2.symm
      | some v => rfl
    · apply Subtype.ext
      funext q
      cases q with
      | none => exact s₂.2.symm
      | some v => rfl

end RootedBlocks
end
end StatMech.FrontierA
