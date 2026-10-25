/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Discrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators

/-- Theorem 5.1.1 (Spencer 1985, "six standard deviations suffice"). Given any system of
$n$ subsets of an $n$-element ground set, there exists a $\pm 1$ colouring $f$ such that
every set has discrepancy at most $6\sqrt n$. -/


noncomputable section

namespace Discrepancy

variable {n m : ℕ}

/-- Indices at which a vector $a \in [-1,1]^m$ is in the open interior, i.e. neither $1$
nor $-1$. The discrepancy argument rounds these to a $\pm 1$ vector. -/
def interiorIndices (a : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => a i ≠ 1 ∧ a i ≠ -1)

/-- Feasibility predicate for the rounding step: a vector $a \in [-1,1]^m$ is feasible
with respect to vectors $v_1, \dots, v_m \in \mathbb{R}^n$ if $\sum_i a_i v_i = 0$. -/
def IsFeasible (v : Fin m → Fin n → ℝ) (a : Fin m → ℝ) : Prop :=
  (∀ i, a i ∈ Set.Icc (-1 : ℝ) 1) ∧ ∑ i, a i • v i = 0

end Discrepancy
end
