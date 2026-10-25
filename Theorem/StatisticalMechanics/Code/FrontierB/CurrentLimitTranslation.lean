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
import Def.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


@[simp] theorem currentShiftFinsetEquiv_val
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (e : ↑(currentShiftFinset g S)) :
    (currentShiftFinsetEquiv g S e).1 = g • e.1 := rfl

@[simp] theorem currentShiftFinsetEquiv_symm_val
    {E H : Type*} [Group H] [MulAction H E] [DecidableEq E]
    (g : H) (S : Finset E) (e : ↑S) :
    ((currentShiftFinsetEquiv g S).symm e).1 = g⁻¹ • e.1 := rfl


end StatMech.FrontierB
