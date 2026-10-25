/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close.Part5
import Mathlib.Combinatorics.Hall.Basic
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def sameOrbit (p q : ConfigSpace α × ConfigSpace α) : Prop :=
  ∀ a, (q.1 a = p.1 a ∧ q.2 a = p.2 a) ∨ (q.1 a = p.2 a ∧ q.2 a = p.1 a)


def orbitKey (p : ConfigSpace α × ConfigSpace α) : ConfigSpace α × ConfigSpace α :=
  (fun a => p.1 a || p.2 a, fun a => p.1 a && p.2 a)

end StatMech
