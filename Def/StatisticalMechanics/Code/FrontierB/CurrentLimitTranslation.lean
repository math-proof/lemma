/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


def currentShiftFinset {E H : Type*} [Group H] [MulAction H E]
    [DecidableEq E] (g : H) (S : Finset E) : Finset E :=
  S.image fun e => g⁻¹ • e


noncomputable def currentShiftFinsetEquiv
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) : ↑(currentShiftFinset g S) ≃ ↑S where
  toFun e := ⟨g • e.1, by
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp e.2
    rw [← hxe, smul_inv_smul]
    exact hx⟩
  invFun e := ⟨g⁻¹ • e.1, Finset.mem_image_of_mem _ e.2⟩
  left_inv e := by ext; simp
  right_inv e := by ext; simp

end StatMech.FrontierB
