/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RecursionTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic


namespace RecursionTheorem

/-- Possible outcomes of running a Turing machine on an input: `accept` (enter
the accept state), `reject` (halt in the reject state) or `diverge` (run
forever). Matches the three TM outcomes described in Sipser's formal
definition. -/
inductive TMResult where
  | accept : TMResult
  | reject : TMResult
  | diverge : TMResult
  deriving DecidableEq

end RecursionTheorem
