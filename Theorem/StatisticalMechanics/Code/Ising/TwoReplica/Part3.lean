/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.TwoReplica.Part3
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (E : Finset (Sym2 V))


lemma oddEdges_subset (m : Current V) : oddEdges E m ⊆ E := Finset.filter_subset _ _


lemma oddEdges_subset_posEdges (m : Current V) : oddEdges E m ⊆ posEdges E m := by
  intro e he
  rw [oddEdges, Finset.mem_filter] at he
  rw [posEdges, Finset.mem_filter]
  exact ⟨he.1, he.2.pos⟩


lemma connOdd_imp_connPos (m : Current V) {u v : V}
    (h : connP (oddEdges E m) u v) : connP (posEdges E m) u v :=
  connP_mono (oddEdges_subset_posEdges E m) h


end Ising
end StatMech
