/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Def.StatisticalMechanics.Code.Sharpness.HighTempPlusBox
open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


theorem plusBoundaryField_nonneg (Lambda : Finset (Site d))
    (x : {v // v ∈ Lambda}) :
    0 ≤ plusBoundaryField Lambda x := by
  simp [plusBoundaryField]


theorem gvBondTouch_endpoint {Lambda : Finset (Site d)} {a b : Site d}
    (he : s(a, b) ∈ gvBondTouch Lambda) : a ∈ Lambda ∨ b ∈ Lambda := by
  rw [gvBondTouch, Finset.mem_image] at he
  obtain ⟨p, hp, hab⟩ := he
  rw [Finset.mem_filter] at hp
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hp.2.2
  · exact hp.2.2.symm


theorem plusBoundary_edge_contribution (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda})
    {e : Sym2 (Site d)} (he : e ∈ plusBoundaryEdges Lambda) :
    (∑ x : {v // v ∈ Lambda}, if x.1 ∈ e then spin tau x else 0) =
      bond (gvGlue (plusField d) Lambda tau) e := by
  rw [plusBoundaryEdges, Finset.mem_filter] at he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab := gvBondTouch_endpoint he.1
      have hnot : ¬ (a ∈ Lambda ∧ b ∈ Lambda) := by
        intro h
        apply he.2
        intro v hv
        rw [Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact h.1
        · exact h.2
      rcases hab with ha | hb
      · have hb' : b ∉ Lambda := fun hb' ↦ hnot ⟨ha, hb'⟩
        have hmem (x : {v // v ∈ Lambda}) :
            (x.1 = a ∨ x.1 = b) ↔ x = ⟨a, ha⟩ := by
          constructor
          · rintro (hxa | hxb)
            · exact Subtype.ext hxa
            · exact absurd (hxb ▸ x.2) hb'
          · rintro rfl
            exact Or.inl rfl
        have hspin : spin (gvGlue (plusField d) Lambda tau) a =
            spin tau ⟨a, ha⟩ := by
          simp [spin, gvGlue, ha]
        simp_rw [Sym2.mem_iff, hmem]
        simp [bond_mk, gvGlue_not_mem, plusField, hb', hspin]
      · have ha' : a ∉ Lambda := fun ha' ↦ hnot ⟨ha', hb⟩
        have hmem (x : {v // v ∈ Lambda}) :
            (x.1 = a ∨ x.1 = b) ↔ x = ⟨b, hb⟩ := by
          constructor
          · rintro (hxa | hxb)
            · exact absurd (hxa ▸ x.2) ha'
            · exact Subtype.ext hxb
          · rintro rfl
            exact Or.inr rfl
        have hspin : spin (gvGlue (plusField d) Lambda tau) b =
            spin tau ⟨b, hb⟩ := by
          simp [spin, gvGlue, hb]
        simp_rw [Sym2.mem_iff, hmem]
        simp [bond_mk, gvGlue_not_mem, plusField, ha', hspin]


theorem plusBoundary_bondSum (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda}) :
    (∑ e ∈ plusBoundaryEdges Lambda,
        bond (gvGlue (plusField d) Lambda tau) e) =
      ∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x := by
  symm
  calc
    (∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x) =
        ∑ x : {v // v ∈ Lambda}, ∑ e ∈ plusBoundaryEdges Lambda,
          if x.1 ∈ e then spin tau x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [plusBoundaryField, Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one]
      rw [Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split <;> simp_all
    _ = ∑ e ∈ plusBoundaryEdges Lambda,
          ∑ x : {v // v ∈ Lambda}, if x.1 ∈ e then spin tau x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ plusBoundaryEdges Lambda,
          bond (gvGlue (plusField d) Lambda tau) e := by
      apply Finset.sum_congr rfl
      intro e he
      exact plusBoundary_edge_contribution Lambda tau he


theorem plusInternalEdges_eq_map (Lambda : Finset (Site d)) :
    (gvBondTouch Lambda).filter (edgeInside Lambda) =
      (graphS d Lambda).edgeFinset.map
        (Function.Embedding.subtype
          (fun x : Site d ↦ x ∈ Lambda)).sym2Map := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [Finset.mem_filter, Finset.mem_map]
      constructor
      · rintro ⟨he, hins⟩
        have ha : a ∈ Lambda :=
          hins a (Sym2.mem_mk_left a b)
        have hb : b ∈ Lambda :=
          hins b (Sym2.mem_mk_right a b)
        refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact gv_bondTouch_subset_edgeSet Lambda s(a, b) he
      · rintro ⟨f, hf, hfe⟩
        induction f using Sym2.inductionOn with
        | _ x y =>
            have hadj : (hypercubicLattice d).Adj x.1 y.1 := by
              rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hf
              exact hf
            have heq : s(a, b) = s(x.1, y.1) := hfe.symm
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · refine ⟨gv_mk_mem_bondTouch hadj (Or.inl x.2), ?_⟩
              intro v hv
              rw [Sym2.mem_iff] at hv
              rcases hv with rfl | rfl
              · exact x.2
              · exact y.2
            · refine ⟨gv_mk_mem_bondTouch hadj.symm (Or.inl y.2), ?_⟩
              intro v hv
              rw [Sym2.mem_iff] at hv
              rcases hv with rfl | rfl
              · exact y.2
              · exact x.2


theorem plusInternal_bondSum (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda}) :
    (∑ e ∈ (gvBondTouch Lambda).filter (edgeInside Lambda),
        bond (gvGlue (plusField d) Lambda tau) e) =
      ∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e := by
  rw [plusInternalEdges_eq_map]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ a b =>
      change bond (gvGlue (plusField d) Lambda tau) s(a.1, b.1) =
        bond tau s(a, b)
      simp [bond_mk, spin, gvGlue, a.2, b.2]


theorem plusTouch_bondSum (Lambda : Finset (Site d))
    (tau : ConfigSpace {v // v ∈ Lambda}) :
    (∑ e ∈ gvBondTouch Lambda,
        bond (gvGlue (plusField d) Lambda tau) e) =
      (∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e) +
        ∑ x : {v // v ∈ Lambda}, plusBoundaryField Lambda x * spin tau x := by
  rw [← plusInternal_bondSum (d := d) Lambda tau,
    ← plusBoundary_bondSum Lambda tau, plusBoundaryEdges]
  exact (Finset.sum_filter_add_sum_filter_not
    (gvBondTouch Lambda) (edgeInside Lambda)
      (fun e ↦ bond (gvGlue (plusField d) Lambda tau) e)).symm


end Sharpness
end StatMech
