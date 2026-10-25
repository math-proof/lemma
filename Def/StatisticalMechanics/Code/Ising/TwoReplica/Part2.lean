/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (E : Finset (Sym2 V))


def adjP (P : Finset (Sym2 V)) (a b : V) : Prop :=
  ∃ e ∈ P, a ∈ e ∧ b ∈ e ∧ a ≠ b


def connP (P : Finset (Sym2 V)) : V → V → Prop :=
  Relation.ReflTransGen (adjP P)

end Ising
end StatMech
