/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossingV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing.Part4
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossingV


namespace StatMech.Onsager.WalkCrossingV

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing

variable {n : ℕ} [NeZero n]


def vertColCross (d : Fin n → Fin 4) (m : ℤ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n =>
    isHorizEdge (d k) ∧ min ((pos d k).1) ((pos d (k + 1)).1) = m)).card


end StatMech.Onsager.WalkCrossingV
