/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter7/RandomGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic
public import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter7.RandomGraphs


public noncomputable section

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
