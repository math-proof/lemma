/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter7/RandomGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter7.RandomGraphs


noncomputable section

open Finset BigOperators

namespace RandomGraphs

/-- An ordered triple of vertices $i < j < k$ in $\text{Fin } n$, used to index
potential triangles in $K_n$. -/
structure Triple (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  hij : i < j
  hjk : j < k
  deriving DecidableEq

end RandomGraphs
end
