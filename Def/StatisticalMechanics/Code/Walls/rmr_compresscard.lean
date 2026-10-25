/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmr_compresscard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
open Finset
open scoped NNReal FinsetFamily


namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


def IsDownAtCoord (i : E) (𝒜 : Finset (ConfigSpace E)) : Prop :=
  ∀ ω ∈ 𝒜, lowerCoord i ω ∈ 𝒜


end StatMech.Walls
