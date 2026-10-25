/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Instance.StatisticalMechanics.Code.Sharpness.ClaimIsing
open Finset SimpleGraph
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem not_edgeInside_compl_of_edgeInside (S : Finset V) (e : Sym2 V)
    (h : edgeInside S e) : ¬ edgeInside Sᶜ e := by
  intro hc
  obtain ⟨⟨a, b⟩, hab⟩ := e.exists_rep
  have ha : a ∈ e := hab ▸ Sym2.mem_mk_left a b
  exact (Finset.mem_compl.mp (hc a ha)) (h a ha)


end Sharpness
end StatMech
