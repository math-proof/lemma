/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JordanParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossing.Part4


namespace StatMech.Onsager.JordanParity

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing

variable {n : ℕ} [NeZero n]


def upCross (d : Fin n → Fin 4) (a b : ℤ) : ℕ :=
  (Finset.univ.filter
    (fun k : Fin n =>
      isHorizEdge (d k) ∧
      min ((pos d k).1) ((pos d (k+1)).1) = a ∧
      b < (pos d k).2)).card


def rayParity (d : Fin n → Fin 4) (a b : ℤ) : ZMod 2 := (upCross d a b : ZMod 2)


end StatMech.Onsager.JordanParity
