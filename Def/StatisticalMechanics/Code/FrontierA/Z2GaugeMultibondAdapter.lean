/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeMultibondAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Abbrev.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]


def anchorConfig (root : V) (s : V → Bool) : AnchoredConfig V root :=
  ⟨fun v => s v ^^ s root, by simp⟩


def unanchorConfig {root : V} (b : Bool) (s : AnchoredConfig V root) : V → Bool :=
  fun v => s.1 v ^^ b


def configEquivBoolAnchored (root : V) :
    (V → Bool) ≃ Bool × AnchoredConfig V root where
  toFun s := (s root, anchorConfig root s)
  invFun bs := unanchorConfig bs.1 bs.2
  left_inv s := by
    funext v
    simp [anchorConfig, unanchorConfig]
  right_inv bs := by
    rcases bs with ⟨b, s⟩
    apply Prod.ext
    · simp [unanchorConfig, s.2]
    · apply Subtype.ext
      funext v
      simp [anchorConfig, unanchorConfig, s.2]


def multibondCut (ends : P → V × V) (s : V → Bool) : Finset P :=
  Finset.univ.filter fun p => s (ends p).1 ≠ s (ends p).2

end
end StatMech.FrontierA
