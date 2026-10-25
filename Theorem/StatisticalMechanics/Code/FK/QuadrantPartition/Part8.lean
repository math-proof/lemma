/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part10
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section BoxGeom

theorem qp_Jset_subset_biUnion (d K : ℕ) :
    qp_Jset d K ⊆ Finset.univ.biUnion (fun i : Fin d => qp_Jslab d K i) := by
  intro x hx
  rw [qp_Jset, Finset.mem_filter] at hx
  obtain ⟨i, hi⟩ := hx.2
  rw [Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, by rw [qp_Jslab, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩⟩

theorem qp_Jslab_card (d K : ℕ) (hd : 1 ≤ d) (i : Fin d) :
    (qp_Jslab d K i).card ≤ (2 * (2 * K + 1) + 1) ^ (d - 1) := by
  classical
  have hsub : (qp_Jslab d K i).image (Subtype.val : boxVerts d (2 * K + 1) → Site d)
      ⊆ Fintype.piFinset (fun j : Fin d =>
          if j = i then ({0} : Finset ℤ) else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hxJ, rfl⟩ := hy
    rw [qp_Jslab, Finset.mem_filter] at hxJ
    rw [Fintype.mem_piFinset]
    intro j; by_cases hj : j = i
    · subst hj; rw [if_pos rfl, Finset.mem_singleton]; exact hxJ.2
    · rw [if_neg hj, Finset.mem_Icc]
      have hb := x.2 j
      have h2 : |(x : Site d) j| ≤ ((2 * K + 1 : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
      have := abs_le.mp h2; push_cast at this ⊢; omega
  calc (qp_Jslab d K i).card
      = ((qp_Jslab d K i).image (Subtype.val : boxVerts d (2 * K + 1) → Site d)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (Fintype.piFinset (fun j : Fin d =>
          if j = i then ({0} : Finset ℤ) else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1))).card :=
        Finset.card_le_card hsub
    _ = ∏ j : Fin d, (if j = i then ({0} : Finset ℤ)
          else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1)).card := Fintype.card_piFinset _
    _ = (2 * (2 * K + 1) + 1) ^ (d - 1) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl,
          Finset.card_singleton, one_mul]
        have hicc : ∀ j ∈ Finset.univ.erase i, (if j = i then ({0} : Finset ℤ)
            else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1)).card = 2 * (2 * K + 1) + 1 := by
          intro j hj; rw [if_neg (Finset.ne_of_mem_erase hj), Int.card_Icc]; omega
        rw [Finset.prod_congr rfl hicc, Finset.prod_const,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]


theorem qp_Jset_card_le (d K : ℕ) (hd : 1 ≤ d) :
    (qp_Jset d K).card ≤ d * (2 * (2 * K + 1) + 1) ^ (d - 1) := by
  calc (qp_Jset d K).card
      ≤ (Finset.univ.biUnion (fun i : Fin d => qp_Jslab d K i)).card :=
        Finset.card_le_card (qp_Jset_subset_biUnion d K)
    _ ≤ ∑ i : Fin d, (qp_Jslab d K i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, (2 * (2 * K + 1) + 1) ^ (d - 1) :=
        Finset.sum_le_sum (fun i _ => qp_Jslab_card d K hd i)
    _ = d * (2 * (2 * K + 1) + 1) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]


theorem qp_boxGraph_degree_le (d n : ℕ) (v : boxVerts d n) : (boxGraph d n).degree v ≤ 2 * d := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  calc ((boxGraph d n).incidenceFinset v).card
      ≤ ((hypercubicLattice d).incidenceFinset (v : Site d)).card := by
        apply Finset.card_le_card_of_injOn (fun e => Sym2.map Subtype.val e)
        · intro e he
          rw [Finset.mem_coe, SimpleGraph.mem_incidenceFinset] at he
          obtain ⟨hmem, hv⟩ := he
          rw [Finset.mem_coe, SimpleGraph.mem_incidenceFinset]
          induction e using Sym2.ind with
          | _ a b =>
            rw [mem_edgeSet] at hmem
            have hadj : (hypercubicLattice d).Adj (a : Site d) (b : Site d) := by
              have : (boxGraph d n).Adj a b := hmem
              simpa only [boxGraph, comap_adj] using this
            refine ⟨?_, ?_⟩
            · simp only [Sym2.map_pair_eq, mem_edgeSet]; exact hadj
            · simp only [Sym2.map_pair_eq]
              rcases Sym2.mem_iff.mp hv with rfl | rfl
              · exact Sym2.mem_mk_left _ _
              · exact Sym2.mem_mk_right _ _
        · intro a _ b _ hab; exact Sym2.map.injective Subtype.val_injective hab
    _ = (hypercubicLattice d).degree (v : Site d) := SimpleGraph.card_incidenceFinset_eq_degree _ _
    _ ≤ 2 * d := degree_le d _


theorem qp_straddle_endpoint_in_J (d K : ℕ) (s : Fin d → Bool) (x y : boxVerts d (2 * K + 1))
    (hadj : (boxGraph d (2 * K + 1)).Adj x y) (hx : qp_boxTag d K x = some s)
    (hy : qp_boxTag d K y ≠ some s) : ∃ i, (y : Site d) i = 0 := by
  by_contra hyc
  push_neg at hyc
  have hyt : qp_boxTag d K y = some (fun i => decide (0 < (y : Site d) i)) := by
    unfold qp_boxTag; rw [if_neg (by push_neg; exact hyc)]
  have hxnz : ∀ i, (x : Site d) i ≠ 0 := by
    intro i hi; unfold qp_boxTag at hx
    by_cases hz : ∃ j, (x : Site d) j = 0
    · rw [if_pos hz] at hx; exact absurd hx (by simp)
    · exact hz ⟨i, hi⟩
  have hxt : qp_boxTag d K x = some (fun i => decide (0 < (x : Site d) i)) := by
    unfold qp_boxTag; rw [if_neg (by push_neg; exact hxnz)]
  rw [hxt, Option.some_inj] at hx
  rw [boxGraph, comap_adj, hypercubicLattice_adj] at hadj
  obtain ⟨i, hi⟩ : ∃ i, ((x : Site d) i - (y : Site d) i).natAbs ≠ 0 := by
    by_contra hc; push_neg at hc; simp only [hc] at hadj; simp at hadj
  have hother : ∀ j ≠ i, (x : Site d) j = (y : Site d) j := by
    intro j hj; by_contra hc
    have : ((x : Site d) i - (y : Site d) i).natAbs + ((x : Site d) j - (y : Site d) j).natAbs
        ≤ ∑ k, ((x : Site d) k - (y : Site d) k).natAbs := by
      rw [show ((x : Site d) i - (y : Site d) i).natAbs + ((x : Site d) j - (y : Site d) j).natAbs
            = ∑ k ∈ ({i, j} : Finset (Fin d)), ((x : Site d) k - (y : Site d) k).natAbs from
          (Finset.sum_pair (f := fun k => ((x : Site d) k - (y : Site d) k).natAbs)
            (Ne.symm hj)).symm]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hjne : 1 ≤ ((x : Site d) j - (y : Site d) j).natAbs := by
      rcases Nat.eq_zero_or_pos ((x : Site d) j - (y : Site d) j).natAbs with h | h
      · exact absurd (by omega : (x : Site d) j = (y : Site d) j) hc
      · omega
    have hine : 1 ≤ ((x : Site d) i - (y : Site d) i).natAbs := Nat.one_le_iff_ne_zero.mpr hi
    omega
  have hsigns : (fun i => decide (0 < (x : Site d) i)) = (fun i => decide (0 < (y : Site d) i)) := by
    funext j; by_cases hj : j = i
    · subst hj
      have hxi := hxnz j; have hyi := hyc j
      have hone : ((x : Site d) j - (y : Site d) j).natAbs = 1 := by
        have heq : ∑ k, ((x : Site d) k - (y : Site d) k).natAbs
            = ((x : Site d) j - (y : Site d) j).natAbs := by
          rw [Finset.sum_eq_single j]
          · intro b _ hb; rw [hother b hb]; simp
          · intro h; exact absurd (Finset.mem_univ _) h
        omega
      have hiff : (0 < (x : Site d) j) ↔ (0 < (y : Site d) j) := by omega
      simp only [hiff]
    · rw [hother j hj]
  rw [hsigns] at hx
  exact hy (hyt.trans (by rw [hx]))


theorem qp_tag_none_iff (d K : ℕ) (x : boxVerts d (2 * K + 1)) :
    qp_boxTag d K x = none ↔ ∃ i, (x : Site d) i = 0 := by
  unfold qp_boxTag
  by_cases hz : ∃ i, (x : Site d) i = 0
  · rw [if_pos hz]; simp [hz]
  · rw [if_neg hz]; simp [hz]


theorem qp_straddle_endpoint_in_J_all (d K : ℕ) (τ : Option (Fin d → Bool))
    (x y : boxVerts d (2 * K + 1)) (hadj : (boxGraph d (2 * K + 1)).Adj x y)
    (hx : qp_boxTag d K x = τ) (hy : qp_boxTag d K y ≠ τ) :
    (∃ i, (x : Site d) i = 0) ∨ (∃ i, (y : Site d) i = 0) := by
  cases τ with
  | none => left; exact (qp_tag_none_iff d K x).mp hx
  | some s => right; exact qp_straddle_endpoint_in_J d K s x y hadj hx hy


theorem qp_straddle_subset_all (d K : ℕ) (τ : Option (Fin d → Bool)) :
    qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ)
      ⊆ (qp_Jset d K).biUnion (fun v => (boxGraph d (2 * K + 1)).incidenceFinset v) := by
  intro e he
  rw [qp_straddleEdges, Finset.mem_filter] at he
  obtain ⟨hedge, hstr⟩ := he
  rw [Finset.mem_biUnion]
  rw [mem_edgeFinset] at hedge
  induction e using Sym2.ind with
  | _ x y =>
    rw [qp_straddleP, Sym2.lift_mk] at hstr
    rw [mem_edgeSet] at hedge
    rcases hstr with ⟨hxq, hyq⟩ | ⟨hxq, hyq⟩
    · rcases qp_straddle_endpoint_in_J_all d K τ x y hedge hxq hyq with ⟨i, hi⟩ | ⟨i, hi⟩
      · refine ⟨x, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_left _ _⟩
      · refine ⟨y, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_right _ _⟩
    · rcases qp_straddle_endpoint_in_J_all d K τ y x hedge.symm hyq hxq with ⟨i, hi⟩ | ⟨i, hi⟩
      · refine ⟨y, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_right _ _⟩
      · refine ⟨x, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_left _ _⟩


theorem qp_straddle_card_le_all (d K : ℕ) (τ : Option (Fin d → Bool)) :
    (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ)).card
      ≤ 2 * d * (qp_Jset d K).card := by
  calc (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ)).card
      ≤ ((qp_Jset d K).biUnion (fun v => (boxGraph d (2 * K + 1)).incidenceFinset v)).card :=
        Finset.card_le_card (qp_straddle_subset_all d K τ)
    _ ≤ ∑ v ∈ qp_Jset d K, ((boxGraph d (2 * K + 1)).incidenceFinset v).card :=
        Finset.card_biUnion_le
    _ = ∑ v ∈ qp_Jset d K, (boxGraph d (2 * K + 1)).degree v :=
        Finset.sum_congr rfl (fun v _ => SimpleGraph.card_incidenceFinset_eq_degree _ v)
    _ ≤ ∑ _v ∈ qp_Jset d K, 2 * d := Finset.sum_le_sum (fun v _ => qp_boxGraph_degree_le _ _ v)
    _ = (qp_Jset d K).card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * d * (qp_Jset d K).card := by ring


theorem qp_blkNone_edge_le (d K : ℕ) :
    (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card
      ≤ 2 * d * (qp_Jset d K).card := by
  calc (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card
      ≤ ((qp_Jset d K).biUnion (fun v => (boxGraph d (2 * K + 1)).incidenceFinset v)).card := by
        apply Finset.card_le_card_of_injOn
          (fun e => Sym2.map (Subtype.val : {x // qp_boxTag d K x = none} → boxVerts d (2 * K + 1)) e)
        · intro e he
          rw [Finset.mem_coe, mem_edgeFinset] at he
          rw [Finset.mem_coe, Finset.mem_biUnion]
          induction e using Sym2.ind with
          | _ a b =>
            rw [mem_edgeSet, qp_blkG, comap_adj] at he
            have haJ : ∃ i, ((a : boxVerts d (2 * K + 1)) : Site d) i = 0 := by
              have ha := a.2; unfold qp_boxTag at ha
              by_cases hz : ∃ i, ((a : boxVerts d (2 * K + 1)) : Site d) i = 0
              · exact hz
              · rw [if_neg hz] at ha; exact absurd ha (by simp)
            refine ⟨(a : boxVerts d (2 * K + 1)),
              by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, haJ⟩, ?_⟩
            rw [SimpleGraph.mem_incidenceFinset]
            simp only [Sym2.map_pair_eq]
            exact ⟨by rw [mem_edgeSet]; exact he, Sym2.mem_mk_left _ _⟩
        · intro a _ b _ hab; exact Sym2.map.injective Subtype.val_injective hab
    _ ≤ ∑ v ∈ qp_Jset d K, ((boxGraph d (2 * K + 1)).incidenceFinset v).card :=
        Finset.card_biUnion_le
    _ = ∑ v ∈ qp_Jset d K, (boxGraph d (2 * K + 1)).degree v :=
        Finset.sum_congr rfl (fun v _ => SimpleGraph.card_incidenceFinset_eq_degree _ v)
    _ ≤ ∑ _v ∈ qp_Jset d K, 2 * d := Finset.sum_le_sum (fun v _ => qp_boxGraph_degree_le _ _ v)
    _ = (qp_Jset d K).card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * d * (qp_Jset d K).card := by ring


end BoxGeom
end FK
end StatMech
