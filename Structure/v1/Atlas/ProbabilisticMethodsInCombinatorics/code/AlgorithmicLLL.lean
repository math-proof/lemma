/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace AlgorithmicLLL

variable {Clause : Type*} {State : Type*}

/-- A `FixSystem` abstracts the structure underlying Moser's algorithm. It consists of
clauses and states, a predicate `satisfied` saying when a clause holds in a state, a `fix`
operation that repairs a clause, the guarantee that `fix c` makes `c` satisfied, and the
invariant that `fix c` preserves all currently satisfied clauses. -/
structure FixSystem (Clause : Type*) (State : Type*) where
  satisfied : Clause → State → Prop
  fix : Clause → State → State
  fix_makes_satisfied : ∀ (c : Clause) (s : State), satisfied c (fix c s)
  fix_preserves_satisfied : ∀ (c d : Clause) (s : State), satisfied d s → satisfied d (fix c s)

end AlgorithmicLLL
