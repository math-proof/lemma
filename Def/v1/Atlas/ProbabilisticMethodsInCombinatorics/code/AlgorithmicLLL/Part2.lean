/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/AlgorithmicLLL.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.AlgorithmicLLL.Part2


namespace AlgorithmicLLL

variable {Clause : Type*} {State : Type*}

variable {sys : FixSystem Clause State}

/-- The number $2^n$ of Boolean assignments on $n$ variables. -/
def numAssignments (n : ℕ) : ℕ := 2 ^ n

/-- Upper bound $2^{\ell(k-1)+1}$ on the number of execution traces of Moser's algorithm of
length $\ell$ on a $k$-CNF formula, used in the entropy-compression argument. -/
def numExecutionTraces (k ℓ : ℕ) : ℕ := 2 ^ (ℓ * (k - 1) + 1)

/-- Combined failure bound $2^n \cdot 2^{\ell(k-1)+1}$ from entropy compression: the count
of (assignment, trace) pairs available to encode failing executions. -/
def failureBound (n k ℓ : ℕ) : ℕ := numAssignments n * numExecutionTraces k ℓ

end AlgorithmicLLL
