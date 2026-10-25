/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RayFlipH.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.JordanParity


namespace StatMech.Onsager.RayFlipH

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


def straddleSet (d : Fin n → Fin 4) (a b : ℤ) : Finset (Fin n) :=
  Finset.univ.filter (fun k : Fin n =>
    isVertEdge (d k) ∧ (pos d k).1 = a + 1 ∧
      min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧ b < max ((pos d k).2) ((pos d (k + 1)).2))


end StatMech.Onsager.RayFlipH
