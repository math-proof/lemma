/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.AlgorithmicLLL


namespace AlgorithmicLLL

variable {Clause : Type*} {State : Type*}

variable {sys : FixSystem Clause State}

/-- A `KCNF` instance: $k$-CNF formula data with `numVars` Boolean variables, `numClauses`
clauses each of width $k \ge 3$, and `maxShared` bounding the number of clauses sharing a
variable with a given clause. -/
structure KCNF where
  numVars : ℕ
  numClauses : ℕ
  k : ℕ
  maxShared : ℕ
  hk : 3 ≤ k
  hn : 0 < numVars

/-- A `MoserKCNF` is a `KCNF` satisfying Moser's sharing condition $\text{maxShared} \le 2^{k-3}$,
the hypothesis under which Moser's algorithm provably finds a satisfying assignment. -/
structure MoserKCNF extends KCNF where
  hshared : maxShared ≤ 2 ^ (k - 3)

end AlgorithmicLLL
