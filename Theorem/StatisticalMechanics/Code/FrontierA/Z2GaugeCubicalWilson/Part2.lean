/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part2
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem mem_gaugeSurfaceBoundary {E P : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P) (e : E) :
    e ∈ gaugeSurfaceBoundary incidence A ↔
      ¬ Even (plaquetteIncidenceCount incidence A e) := by
  simp [gaugeSurfaceBoundary]


theorem isClosedPlaquetteSet_iff_gaugeSurfaceBoundary_eq_empty
    {E P : Type*} [Fintype E] [DecidableEq E] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P) :
    IsClosedPlaquetteSet incidence A ↔
      gaugeSurfaceBoundary incidence A = ∅ := by
  constructor
  · intro hclosed
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨e, he⟩
    exact (mem_gaugeSurfaceBoundary incidence A e).mp he (hclosed e)
  · intro hempty e
    by_contra hodd
    have hmem : e ∈ gaugeSurfaceBoundary incidence A := by
      simpa using hodd
    rw [hempty] at hmem
    simp at hmem


theorem hasWilsonBoundary_gaugeSurfaceBoundary {E P : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq P]
    (incidence : P → Finset E) (A : Finset P) :
    HasWilsonBoundary incidence A (gaugeSurfaceBoundary incidence A) := by
  intro e
  by_cases heven : Even (plaquetteIncidenceCount incidence A e)
  · have hnotmem : e ∉ gaugeSurfaceBoundary incidence A := by
      simpa using heven
    simp only [hnotmem, if_false, add_zero]
    exact heven
  · have hmem : e ∈ gaugeSurfaceBoundary incidence A := by
      simpa using heven
    simp only [hmem, if_true]
    exact Nat.even_add_one.mpr heven


theorem gaugeSurfaceBoundary_singleton {E P : Type*}
    [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P]
    (incidence : P → Finset E) (p : P) :
    gaugeSurfaceBoundary incidence {p} = incidence p := by
  ext e
  rw [mem_gaugeSurfaceBoundary, plaquetteIncidenceCount_eq_filter_card]
  by_cases he : e ∈ incidence p
  · have hfilter : ({q ∈ ({p} : Finset P) | e ∈ incidence q}) = {p} := by
      apply Finset.filter_eq_self.mpr
      intro q hq
      simp only [mem_singleton] at hq
      subst q
      exact he
    rw [hfilter]
    norm_num [he]
  · have hfilter : ({q ∈ ({p} : Finset P) | e ∈ incidence q}) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro q hq
      simp only [mem_singleton] at hq
      subst q
      exact he
    rw [hfilter]
    norm_num [he]


end
end StatMech.FrontierA
