/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.RelClasses


namespace TuringMachine

/-- The two possible directions in which a Turing machine head can move on each
step: `L` for left, `R` for right. -/
inductive Direction where
  | L : Direction
  | R : Direction
  deriving DecidableEq, Repr, Inhabited

end TuringMachine
