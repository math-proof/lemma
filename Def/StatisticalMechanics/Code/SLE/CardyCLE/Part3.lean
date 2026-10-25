/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
import Inductive.StatisticalMechanics.Code.SLE.CardyCLE
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

noncomputable def slePhase (κ : ℝ) : SLEPhase :=
  if κ ≤ 4 then SLEPhase.simple
  else if κ < 8 then SLEPhase.selfTouching
  else SLEPhase.spaceFilling


end StatMech.SLE
