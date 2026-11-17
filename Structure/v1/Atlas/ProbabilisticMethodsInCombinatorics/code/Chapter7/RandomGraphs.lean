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


public noncomputable section

open Finset BigOperators

namespace RandomGraphs

/-- An (unordered) edge of $K_n$ encoded as an ordered pair $\text{src} < \text{dst}$
of vertices in $\text{Fin } n$. -/
structure Edge (n : ℕ) where
  src : Fin n
  dst : Fin n
  hlt : src < dst
  deriving DecidableEq

end RandomGraphs
end
