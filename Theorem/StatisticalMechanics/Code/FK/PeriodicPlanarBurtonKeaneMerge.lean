/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneCore.Part3
open MeasureTheory Set SimpleGraph
open scoped ENNReal


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

@[simp] theorem forceOpenFinset_of_mem {F : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∈ F) (omega : ConfigSpace (Sym2 V)) :
    forceOpenFinset F omega e = true := by
  simp [forceOpenFinset, he]

@[simp] theorem forceOpenFinset_of_notMem {F : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∉ F) (omega : ConfigSpace (Sym2 V)) :
    forceOpenFinset F omega e = omega e := by
  simp [forceOpenFinset, he]

theorem forceOpenFinset_le (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V)) : omega <= forceOpenFinset F omega := by
  intro e
  by_cases he : e ∈ F <;> simp [forceOpenFinset, he]

omit [Countable V] in
theorem PeriodicGraph.openSubgraph_mono (P : PeriodicGraph V)
    {omega eta : ConfigSpace (Sym2 V)} (h : omega <= eta) :
    P.openSubgraph omega <= P.openSubgraph eta := by
  intro x y hxy
  rw [P.openSubgraph_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  have he := h s(x, y)
  rw [hxy.2] at he
  exact le_antisymm (by simp) he

omit [Countable V] in
theorem PeriodicGraph.reachable_mono (P : PeriodicGraph V)
    {omega eta : ConfigSpace (Sym2 V)} (h : omega <= eta) {x y : V}
    (hxy : (P.openSubgraph omega).Reachable x y) :
    (P.openSubgraph eta).Reachable x y :=
  hxy.mono (P.openSubgraph_mono h)

omit [Countable V] in
theorem PeriodicGraph.cluster_mono (P : PeriodicGraph V)
    {omega eta : ConfigSpace (Sym2 V)} (h : omega <= eta) (x : V) :
    P.cluster omega x ⊆ P.cluster eta x := fun _ hxy => P.reachable_mono h hxy

theorem encard_image_lt_of_not_injOn_periodic
    {A B : Type*} {s : Set A} {f : A -> B}
    (hfin : s.Finite) (hni : ¬ Set.InjOn f s) :
    (f '' s).encard < s.encard := by
  rcases lt_or_eq_of_le (Set.encard_image_le f s) with h | h
  · exact h
  · exact False.elim (hni (hfin.injOn_of_encard_image_eq h))

end StatMech.FK.PeriodicPlanar
