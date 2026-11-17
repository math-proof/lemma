/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA211417_supercongruence_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.FC.OeisA211417_supercongruence_solution

@[expose] public section

namespace OeisA211417

open Nat Int Finset

noncomputable instance unitIndexFintype (p k : ℕ) : Fintype (unitIndex p k) := by
  unfold unitIndex
  infer_instance

end OeisA211417
