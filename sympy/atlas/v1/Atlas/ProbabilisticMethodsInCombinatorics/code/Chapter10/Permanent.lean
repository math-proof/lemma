/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/Permanent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

open Finset Matrix BigOperators

namespace BregmanMinc

/-- The row sum $d_i$ of row $i$ of a $0/1$-matrix $A$: the number of columns $j$ with $A_{ij}=1$. -/
noncomputable def rowSum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => A i j = 1)).card

/-- Logarithmic form of the Brégman-Minc inequality (Theorem 10.2.1): for a $0/1$-matrix $A$
with positive permanent, $\log \operatorname{per} A \le \sum_i \frac{1}{d_i} \log(d_i!)$. -/
noncomputable def rowSumGen {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (i : V) : ℕ :=
  (Finset.univ.filter (fun j => A i j = 1)).card

/-- Brégman-Minc inequality for matrices indexed by an arbitrary finite type $V$:
$\operatorname{per} A \le \prod_{i \in V} (d_i!)^{1/d_i}$ for $0/1$-matrices $A$. -/
end BregmanMinc

namespace KahnLovasz

open SimpleGraph Finset BigOperators

/-- The number of perfect matchings of a simple graph $G$. -/
noncomputable def numPerfectMatchings {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card {M : G.Subgraph // M.IsPerfectMatching}
