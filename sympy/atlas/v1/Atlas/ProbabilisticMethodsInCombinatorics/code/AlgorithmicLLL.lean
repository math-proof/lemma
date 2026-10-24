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

variable {sys : FixSystem Clause State}

/-- `IsValidOuterLoop sys cs s` says that the list of clauses `cs` is a valid execution
trace of the outer loop of Moser's algorithm starting from state `s`: each successive
clause is unsatisfied at the moment it is visited and then fixed. -/
def IsValidOuterLoop (sys : FixSystem Clause State) :
    List Clause → State → Prop
  | [], _ => True
  | c :: cs, s => ¬sys.satisfied c s ∧ IsValidOuterLoop sys cs (sys.fix c s)

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

/-- The number $2^n$ of Boolean assignments on $n$ variables. -/
def numAssignments (n : ℕ) : ℕ := 2 ^ n

/-- Upper bound $2^{\ell(k-1)+1}$ on the number of execution traces of Moser's algorithm of
length $\ell$ on a $k$-CNF formula, used in the entropy-compression argument. -/
def numExecutionTraces (k ℓ : ℕ) : ℕ := 2 ^ (ℓ * (k - 1) + 1)

/-- Combined failure bound $2^n \cdot 2^{\ell(k-1)+1}$ from entropy compression: the count
of (assignment, trace) pairs available to encode failing executions. -/
def failureBound (n k ℓ : ℕ) : ℕ := numAssignments n * numExecutionTraces k ℓ
