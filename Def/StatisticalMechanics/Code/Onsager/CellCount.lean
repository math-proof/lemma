/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech.Onsager.CellCount

open Finset


def cornersOf (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {c, (c.1 + 1, c.2), (c.1, c.2 + 1), (c.1 + 1, c.2 + 1)}


def cornerCount (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : ℕ :=
  (S.filter (fun c => v ∈ cornersOf c)).card


def cellVerts (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.biUnion cornersOf


end StatMech.Onsager.CellCount
