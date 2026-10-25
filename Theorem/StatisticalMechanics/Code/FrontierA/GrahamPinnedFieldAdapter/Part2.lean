/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamHeadlineAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGTriangle
import Def.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem grahamPinConfig_at (m : V) (t : ConfigSpace V) :
    grahamPinConfig m t m = true := by
  simp [grahamPinConfig]

@[simp] theorem grahamPinConfig_of_ne (m : V) (t : ConfigSpace V)
    {x : V} (hxm : x ≠ m) :
    grahamPinConfig m t x = t x := by
  simp [grahamPinConfig, hxm]

theorem spin_grahamPinConfig_at (m : V) (t : ConfigSpace V) :
    spin (grahamPinConfig m t) m = 1 := by
  simp [spin]

theorem spin_grahamPinConfig_of_ne (m : V) (t : ConfigSpace V)
    {x : V} (hxm : x ≠ m) :
    spin (grahamPinConfig m t) x = spin t x := by
  simp [spin, grahamPinConfig, hxm]


theorem grahamAnchor_incidentSum
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V) (t : ConfigSpace V) :
    (∑ e ∈ E.filter (fun e => m ∈ e),
        J e * bond (grahamPinConfig m t) e) =
      ∑ x, grahamAnchorField E J m x * spin t x := by
  classical
  let N : Finset V := Finset.univ.filter (fun x => x ≠ m ∧ s(x, m) ∈ E)
  have hfield :
      (∑ x, grahamAnchorField E J m x * spin t x) =
        ∑ x ∈ N, J s(x, m) * spin t x := by
    classical
    simp only [N, Finset.sum_filter, Finset.mem_univ, true_and]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxm : x = m
    · simp [grahamAnchorField, hxm]
    · by_cases hE : s(x, m) ∈ E <;> simp [grahamAnchorField, hxm, hE]
  rw [hfield]
  symm
  apply Finset.sum_bij (fun x _ => s(x, m))
  · intro x hx
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter]
    exact ⟨hx.2, Sym2.mem_mk_right x m⟩
  · intro x hx y hy hxy
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    rw [Sym2.eq_iff] at hxy
    rcases hxy with h | h
    · exact h.1
    · exact False.elim (hx.1 h.1)
  · intro e he
    simp only [Finset.mem_filter] at he
    induction e using Sym2.ind with
    | _ x y =>
        simp only [Sym2.mem_iff] at he
        rcases he.2 with rfl | rfl
        · refine ⟨y, ?_, by simpa [Sym2.eq_swap]⟩
          have hne : y ≠ m := by
            intro hym
            subst y
            exact hdiag s(m, m) he.1 (Sym2.mk_isDiag_iff.mpr rfl)
          simp [N, hne, he.1, Sym2.eq_swap]
        · refine ⟨x, ?_, rfl⟩
          have hne : x ≠ m := by
            intro hxm
            subst x
            exact hdiag s(m, m) he.1 (Sym2.mk_isDiag_iff.mpr rfl)
          simp [N, hne, he.1]
  · intro x hx
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [bond_mk, spin_grahamPinConfig_of_ne m t hx.1,
      spin_grahamPinConfig_at]
    ring


theorem grahamAnchor_nonincidentSum
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (m : V) (t : ConfigSpace V) :
    (∑ e ∈ E, grahamAnchorCoupling J m e * bond t e) =
      ∑ e ∈ E.filter (fun e => m ∉ e), J e * bond t e := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hme : m ∈ e <;> simp [grahamAnchorCoupling, hme]


theorem grahamAnchor_weight_eq_pin
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (hdiag : ∀ e ∈ E, ¬ e.IsDiag) (m : V) (t : ConfigSpace V) :
    wJ E (grahamAnchorCoupling J m) (grahamAnchorField E J m) t =
      wJ E J (fun _ => 0) (grahamPinConfig m t) := by
  unfold wJ
  congr 1
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [grahamAnchor_nonincidentSum, ← grahamAnchor_incidentSum E J hdiag]
  have hnonincident :
      (∑ e ∈ E.filter (fun e => m ∉ e),
          J e * bond (grahamPinConfig m t) e) =
        ∑ e ∈ E.filter (fun e => m ∉ e), J e * bond t e := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [Finset.mem_filter] at he
    induction e using Sym2.ind with
    | _ x y =>
        simp only [Sym2.mem_iff, not_or] at he
        have hxm : x ≠ m := fun h => he.2.1 h.symm
        have hym : y ≠ m := fun h => he.2.2 h.symm
        rw [bond_mk, bond_mk, spin_grahamPinConfig_of_ne m t hxm,
          spin_grahamPinConfig_of_ne m t hym]
  rw [← hnonincident]
  have hsplit := Finset.sum_filter_add_sum_filter_not E
    (fun e => m ∈ e) (fun e => J e * bond (grahamPinConfig m t) e)
  simpa only [add_comm] using hsplit


end StatMech.FrontierA
