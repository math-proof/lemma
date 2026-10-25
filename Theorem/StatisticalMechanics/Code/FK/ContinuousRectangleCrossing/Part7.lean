/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part7
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


theorem continuous_normalizeRectangle (a b c d : ℝ) :
    Continuous (normalizeRectangle a b c d) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [normalizeRectangle] <;> fun_prop

theorem normalizeRectangle_injective {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Function.Injective (normalizeRectangle a b c d) := by
  intro p q hpq
  funext i
  have hi := congrFun hpq i
  fin_cases i
  · simp [normalizeRectangle] at hi
    field_simp [ne_of_gt (sub_pos.mpr hab)] at hi
    simpa using (sub_left_inj.mp hi)
  · simp [normalizeRectangle] at hi
    field_simp [ne_of_gt (sub_pos.mpr hcd)] at hi
    simpa using (sub_left_inj.mp hi)

theorem normalizeRectangle_mem_unitSquare {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) {p : Fin 2 → ℝ}
    (hp : InRectangle a b c d p) :
    InUnitSquare (normalizeRectangle a b c d p) := by
  intro i
  fin_cases i
  · change 0 ≤ (p 0 - a) / (b - a) ∧ (p 0 - a) / (b - a) ≤ 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr hp.1) (sub_pos.mpr hab).le
    · rw [div_le_one (sub_pos.mpr hab)]
      linarith [hp.2.1]
  · change 0 ≤ (p 1 - c) / (d - c) ∧ (p 1 - c) / (d - c) ≤ 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr hp.2.2.1) (sub_pos.mpr hcd).le
    · rw [div_le_one (sub_pos.mpr hcd)]
      linarith [hp.2.2.2]


theorem rectangle_paths_intersect
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hgamma : Set.range gamma ⊆ {x | InRectangle a b c d x})
    (heta : Set.range eta ⊆ {x | InRectangle a b c d x})
    (hl0 : hl 0 = a) (hr0 : hr 0 = b)
    (vb1 : vb 1 = c) (vt1 : vt 1 = d) :
    ∃ t s : unitInterval, gamma t = eta s := by
  let ngamma := gamma.map (continuous_normalizeRectangle a b c d)
  let neta := eta.map (continuous_normalizeRectangle a b c d)
  have hngamma : Set.range ngamma ⊆ {x | InUnitSquare x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    exact normalizeRectangle_mem_unitSquare hab hcd (hgamma ⟨t, rfl⟩)
  have hneta : Set.range neta ⊆ {x | InUnitSquare x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    exact normalizeRectangle_mem_unitSquare hab hcd (heta ⟨t, rfl⟩)
  have hnl : (normalizeRectangle a b c d hl) 0 = 0 := by
    simp [normalizeRectangle, hl0]
  have hnr : (normalizeRectangle a b c d hr) 0 = 1 := by
    simp [normalizeRectangle, hr0, ne_of_gt (sub_pos.mpr hab)]
  have hnb : (normalizeRectangle a b c d vb) 1 = 0 := by
    simp [normalizeRectangle, vb1]
  have hnt : (normalizeRectangle a b c d vt) 1 = 1 := by
    simp [normalizeRectangle, vt1, ne_of_gt (sub_pos.mpr hcd)]
  obtain ⟨t, s, hts⟩ := unitSquare_paths_intersect ngamma neta
    hngamma hneta hnl hnr hnb hnt
  refine ⟨t, s, ?_⟩
  exact normalizeRectangle_injective hab hcd hts


end ContinuousRectangleCrossing
end StatMech
