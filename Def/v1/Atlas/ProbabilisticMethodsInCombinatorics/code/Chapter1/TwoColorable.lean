/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/TwoColorable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Abbrev.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable
open Finset Fintype


namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge `e` is monochromatic under a 2-coloring `c` if all its vertices share the
same color. -/
def IsMonochromatic (e : Finset V) (c : V → Bool) : Prop :=
  (∀ v ∈ e, c v = true) ∨ (∀ v ∈ e, c v = false)

end TwoColorableHypergraph
