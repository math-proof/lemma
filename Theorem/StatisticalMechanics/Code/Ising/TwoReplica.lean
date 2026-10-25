/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.TwoReplica
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (E : Finset (Sym2 V))


@[simp] lemma mem_sources {n : Current V} {x : V} :
    x ∈ sources E n ↔ Odd (incidentFlux E n x) := by simp [sources]


lemma incidentFlux_add (n m : Current V) (x : V) :
    incidentFlux E (fun e => n e + m e) x
      = incidentFlux E n x + incidentFlux E m x := by
  unfold incidentFlux; rw [← Finset.sum_add_distrib]


lemma sources_add (n m : Current V) :
    sources E (fun e => n e + m e) = sources E n ∆ sources E m := by
  ext x
  simp only [mem_sources, incidentFlux_add, Finset.mem_symmDiff]
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    ← ZMod.natCast_eq_one_iff_odd]
  push_cast
  generalize (incidentFlux E n x : ZMod 2) = a
  generalize (incidentFlux E m x : ZMod 2) = b
  revert a b; decide


end Ising
end StatMech
