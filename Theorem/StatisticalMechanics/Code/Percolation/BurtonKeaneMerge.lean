/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


@[simp] lemma forceOpenFinset_of_mem {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)}
    (h : e ∈ F) (ω : ConfigSpace (Sym2 (Site d))) : forceOpenFinset F ω e = true := by
  simp [forceOpenFinset, h]

@[simp] lemma forceOpenFinset_of_notMem {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)}
    (h : e ∉ F) (ω : ConfigSpace (Sym2 (Site d))) : forceOpenFinset F ω e = ω e := by
  simp [forceOpenFinset, h]


lemma forceOpenFinset_le (F : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) :
    ω ≤ forceOpenFinset F ω := by
  intro e; unfold forceOpenFinset; by_cases h : e ∈ F <;> simp [h]


theorem measurable_forceOpenFinset (F : Finset (Sym2 (Site d))) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => forceOpenFinset F ω) := by
  apply measurable_pi_lambda
  intro e
  unfold forceOpenFinset
  by_cases h : e ∈ F
  · simp [h]
  · simp only [h, if_false]; exact measurable_pi_apply e


lemma openSubgraph_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (hle : ω ≤ ω') :
    openSubgraph d ω ≤ openSubgraph d ω' := by
  intro x y h
  rw [openSubgraph_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  have := hle s(x, y); rw [h.2] at this; exact le_antisymm (by simp) this


lemma connected_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (hle : ω ≤ ω')
    {x y : Site d} (h : Connected d ω x y) : Connected d ω' x y :=
  h.mono (openSubgraph_mono hle)


lemma cluster_mono {ω ω' : ConfigSpace (Sym2 (Site d))} (hle : ω ≤ ω') (x : Site d) :
    cluster d ω x ⊆ cluster d ω' x := fun _ hy => connected_mono hle hy


theorem encard_image_lt_of_not_injOn {α β : Type*} {s : Set α} {f : α → β}
    (hfin : s.Finite) (hni : ¬ Set.InjOn f s) :
    (f '' s).encard < s.encard := by
  rcases lt_or_eq_of_le (Set.encard_image_le f s) with h | h
  · exact h
  · exact absurd (hfin.injOn_of_encard_image_eq h) hni


end Percolation
end StatMech
