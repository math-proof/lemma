/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA211417_supercongruence_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA211417_supercongruence_solution.Part2


namespace OeisA211417

open Nat Int Finset

noncomputable instance unitIndexDecidableEq (p k : ℕ) :
    DecidableEq (unitIndex p k) := Classical.decEq _

end OeisA211417
