/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith


namespace HasseWalks

inductive HStep : Type where
  | U : HStep
  | D : HStep
  deriving DecidableEq, Repr

end HasseWalks
