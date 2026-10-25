/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PrefixCoversClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachDomination.Part3
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace PrefixCoversClose

open OSSS.Coding

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.ReachDomination

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem reachOpen_mono {endU endV : E → V} {X w : ConfigSpace E}
    (hle : ∀ e, X e = true → w e = true) {x y : V}
    (h : ReachOpen endU endV X x y) : ReachOpen endU endV w x y := by
  induction h with
  | refl x => exact ReachOpen.refl x
  | step e hopen hpair _ ih => exact ReachOpen.step e (hle e hopen) hpair ih

omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem connOpenSet_mono {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hle : ∀ e, X e = true → w e = true) {x : V}
    (h : ConnOpenSet endU endV X x B) : ConnOpenSet endU endV w x B := by
  obtain ⟨b, hbB, hreach⟩ := h
  exact ⟨b, hbB, reachOpen_mono hle hreach⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem incidentCluster_mono {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hle : ∀ e, X e = true → w e = true) {e' : E}
    (h : IncidentCluster endU endV X B e') : IncidentCluster endU endV w B e' := by
  rcases h with hU | hV
  · exact Or.inl (connOpenSet_mono hle hU)
  · exact Or.inr (connOpenSet_mono hle hV)


end PrefixCoversClose
end OSSS
end StatMech
