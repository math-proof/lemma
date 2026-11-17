/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Tactic.Linarith


namespace HasseWalks

public inductive HStep : Type where
  | U : HStep
  | D : HStep
  deriving DecidableEq, Repr

end HasseWalks
