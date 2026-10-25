/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.FrontierA.GrahamThreeGateBoundaryCounterexample.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


theorem canonicalGateCounter_closed
    (E : Finset (Fin 21)) (C : Finset (Fin 7))
    (hEC :
      ((E = canonicalGateCounterK ∨ E = canonicalGateCounterS) ∧ C = {0, 1}) ∨
      ((E = canonicalGateCounterL ∨ E = canonicalGateCounterR) ∧ C = {1, 2})) :
    ∀ i ∈ E, ∀ a ∈ canonicalGateCounterEnds i, a ∈ C ->
      ∀ b ∈ canonicalGateCounterEnds i, b ∈ C := by
  rcases hEC with ⟨hE, rfl⟩ | ⟨hE, rfl⟩ <;>
    rcases hE with rfl | rfl <;>
    intro i hi a ha haC b hb <;>
    fin_cases i <;>
    simp [canonicalGateCounterK, canonicalGateCounterL,
      canonicalGateCounterS, canonicalGateCounterR,
      canonicalGateCounterEnds] at hi ha haC hb ⊢ <;> aesop

theorem canonicalGateCounter_not_conn
    (E : Finset (Fin 21)) (C : Finset (Fin 7))
    (hEC :
      ((E = canonicalGateCounterK ∨ E = canonicalGateCounterS) ∧ C = {0, 1}) ∨
      ((E = canonicalGateCounterL ∨ E = canonicalGateCounterR) ∧ C = {1, 2})) :
    ¬ connK canonicalGateCounterEnds E 1 3 := by
  apply not_connK_of_closed_vertex_set (C := C)
  · rcases hEC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  · rcases hEC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  · exact canonicalGateCounter_closed E C hEC

theorem canonicalGateCounter_rows_partition :
    canonicalGateCounterSupport \ canonicalGateCounterK = canonicalGateCounterL ∧
      canonicalGateCounterSupport \ canonicalGateCounterA = canonicalGateCounterB ∧
      canonicalGateCounterSupport \ canonicalGateCounterS = canonicalGateCounterR := by
  decide

theorem canonicalGateCounter_cells :
    canonicalGateCounterK ∩ canonicalGateCounterA = canonicalGateCounterC0 ∧
      canonicalGateCounterK ∩ canonicalGateCounterB = canonicalGateCounterC1 ∧
      canonicalGateCounterL ∩ canonicalGateCounterA = canonicalGateCounterC2 ∧
      canonicalGateCounterL ∩ canonicalGateCounterB = canonicalGateCounterC3 := by
  decide

theorem canonicalGateCounter_cell_sources :
    sources canonicalGateCounterEnds canonicalGateCounterC0 = {0, 1} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC1 = ∅ ∧
      sources canonicalGateCounterEnds canonicalGateCounterC2 = {1, 2} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC3 = ∅ := by
  decide

theorem canonicalGateCounter_K_no_incident_three :
    ∀ i ∈ canonicalGateCounterK,
      (3 : Fin 7) ∉ canonicalGateCounterEnds i := by
  intro i hi
  fin_cases i <;>
    simp [canonicalGateCounterK, canonicalGateCounterEnds] at hi ⊢

theorem edgeComponent_subset_support_generic
    {I W : Type*} [DecidableEq I] [Fintype W] [DecidableEq W]
    (ends : I -> Sym2 W) (E : Finset I) (u : W) :
    edgeComponent ends E u ⊆ E := by
  classical
  intro i hi
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.1

theorem edgeComponent_endpoint_conn_generic
    {I W : Type*} [DecidableEq I] [Fintype W] [DecidableEq W]
    (ends : I -> Sym2 W) (E : Finset I) (u : W)
    {i : I} (hi : i ∈ edgeComponent ends E u)
    {x : W} (hx : x ∈ ends i) :
    connK ends E u x := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.2 x hx

theorem canonicalGateCounter_K_zeroComponent :
    edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  let x := (canonicalGateCounterEnds i).out.1
  have hx : x ∈ canonicalGateCounterEnds i :=
    Sym2.out_fst_mem (canonicalGateCounterEnds i)
  have h3x : (3 : Fin 7) ≠ x := by
    intro h
    have h3mem : (3 : Fin 7) ∈ canonicalGateCounterEnds i := by
      rw [h]
      exact hx
    exact canonicalGateCounter_K_no_incident_three i
      (edgeComponent_subset_support_generic _ _ _ hi) h3mem
  exact (not_connK_of_no_incident h3x
    canonicalGateCounter_K_no_incident_three)
      (edgeComponent_endpoint_conn_generic _ _ _ hi hx)

theorem canonicalGateCounter_L_closed :
    ∀ i ∈ canonicalGateCounterL,
      ∀ a ∈ canonicalGateCounterEnds i, a ∈ ({1, 2} : Finset (Fin 7)) ->
      ∀ b ∈ canonicalGateCounterEnds i, b ∈ ({1, 2} : Finset (Fin 7)) := by
  exact canonicalGateCounter_closed _ _
    (Or.inr ⟨Or.inl rfl, rfl⟩)

theorem canonicalGateCounter_L_not_conn_outside
    {x : Fin 7} (hx : x ∉ ({1, 2} : Finset (Fin 7))) :
    ¬ connK canonicalGateCounterEnds canonicalGateCounterL 1 x := by
  apply not_connK_of_closed_vertex_set
    (C := ({1, 2} : Finset (Fin 7))) (by simp) hx
  exact canonicalGateCounter_L_closed

theorem canonicalGateCounter_L_edge_outside_of_ne_six
    (i : Fin 21) (hi : i ∈ canonicalGateCounterL) (hne : i ≠ 6) :
    ∃ x ∈ canonicalGateCounterEnds i,
      x ∉ ({1, 2} : Finset (Fin 7)) := by
  fin_cases i <;>
    simp [canonicalGateCounterL, canonicalGateCounterEnds] at hi hne ⊢

theorem canonicalGateCounter_L_kComponent :
    edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 = {6} := by
  classical
  apply Finset.Subset.antisymm
  · intro i hi
    by_cases h : i = 6
    · simp [h]
    · obtain ⟨x, hx, hxout⟩ :=
        canonicalGateCounter_L_edge_outside_of_ne_six i
          (by
            exact edgeComponent_subset_support_generic _ _ _ hi) h
      exfalso
      apply canonicalGateCounter_L_not_conn_outside hxout
      exact edgeComponent_endpoint_conn_generic _ _ _ hi hx
  · intro i hi
    have hi6 : i = 6 := by simpa using hi
    subst i
    exact mem_edgeComponent_of_endpoint
      (by simp [canonicalGateCounterL])
      (by simp [canonicalGateCounterEnds])

theorem canonicalGateCounter_transfer_is_canonical :
    edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 ∪
        edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 =
      canonicalGateCounterTransfer := by
  rw [canonicalGateCounter_K_zeroComponent,
    canonicalGateCounter_L_kComponent]
  rfl

theorem canonicalGateCounter_transfer_rows :
    canonicalGateCounterA ∆ canonicalGateCounterTransfer =
        canonicalGateCounterS ∧
      canonicalGateCounterB ∆ canonicalGateCounterTransfer =
        canonicalGateCounterR := by
  decide

theorem canonicalGateCounter_KL_gated :
    CanonicalGateCounterGated canonicalGateCounterK := by
  rw [CanonicalGateCounterGated, canonicalGateCounter_rows_partition.1]
  exact ⟨canonicalGateCounter_not_conn _ _
      (Or.inl ⟨Or.inl rfl, rfl⟩),
    canonicalGateCounter_not_conn _ _
      (Or.inr ⟨Or.inl rfl, rfl⟩)⟩

theorem canonicalGateCounter_SR_gated :
    CanonicalGateCounterGated canonicalGateCounterS := by
  rw [CanonicalGateCounterGated, canonicalGateCounter_rows_partition.2.2]
  exact ⟨canonicalGateCounter_not_conn _ _
      (Or.inl ⟨Or.inr rfl, rfl⟩),
    canonicalGateCounter_not_conn _ _
      (Or.inr ⟨Or.inr rfl, rfl⟩)⟩

theorem canonicalGateCounter_A_conn :
    connK canonicalGateCounterEnds canonicalGateCounterA 1 3 := by
  have h12 : connK canonicalGateCounterEnds canonicalGateCounterA 1 2 :=
    Relation.ReflTransGen.single ⟨6, by simp [canonicalGateCounterA],
      by simp [canonicalGateCounterEnds], by simp [canonicalGateCounterEnds], by decide⟩
  have h25 : adjStep canonicalGateCounterEnds canonicalGateCounterA 2 5 :=
    ⟨13, by simp [canonicalGateCounterA], by simp [canonicalGateCounterEnds],
      by simp [canonicalGateCounterEnds], by decide⟩
  have h53 : adjStep canonicalGateCounterEnds canonicalGateCounterA 5 3 :=
    ⟨16, by simp [canonicalGateCounterA], by simp [canonicalGateCounterEnds],
      by simp [canonicalGateCounterEnds], by decide⟩
  exact (h12.tail h25).tail h53


theorem canonicalGate_cellStrengthening_not_sufficient :
    canonicalGateCounterK ∩ canonicalGateCounterA = canonicalGateCounterC0 ∧
      canonicalGateCounterK ∩ canonicalGateCounterB = canonicalGateCounterC1 ∧
      canonicalGateCounterL ∩ canonicalGateCounterA = canonicalGateCounterC2 ∧
      canonicalGateCounterL ∩ canonicalGateCounterB = canonicalGateCounterC3 ∧
      sources canonicalGateCounterEnds canonicalGateCounterC0 = {0, 1} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC1 = ∅ ∧
      sources canonicalGateCounterEnds canonicalGateCounterC2 = {1, 2} ∧
      sources canonicalGateCounterEnds canonicalGateCounterC3 = ∅ ∧
      (edgeComponent canonicalGateCounterEnds canonicalGateCounterK 3 ∪
          edgeComponent canonicalGateCounterEnds canonicalGateCounterL 1 =
        canonicalGateCounterTransfer) ∧
      canonicalGateCounterA ∆ canonicalGateCounterTransfer =
        canonicalGateCounterS ∧
      canonicalGateCounterB ∆ canonicalGateCounterTransfer =
        canonicalGateCounterR ∧
      CanonicalGateCounterGated canonicalGateCounterK ∧
      CanonicalGateCounterGated canonicalGateCounterS ∧
      ¬ CanonicalGateCounterGated canonicalGateCounterA := by
  refine ⟨canonicalGateCounter_cells.1,
    canonicalGateCounter_cells.2.1,
    canonicalGateCounter_cells.2.2.1,
    canonicalGateCounter_cells.2.2.2,
    canonicalGateCounter_cell_sources.1,
    canonicalGateCounter_cell_sources.2.1,
    canonicalGateCounter_cell_sources.2.2.1,
    canonicalGateCounter_cell_sources.2.2.2,
    canonicalGateCounter_transfer_is_canonical,
    canonicalGateCounter_transfer_rows.1,
    canonicalGateCounter_transfer_rows.2,
    canonicalGateCounter_KL_gated,
    canonicalGateCounter_SR_gated, ?_⟩
  intro hA
  exact hA.1 canonicalGateCounter_A_conn

end StatMech.GrahamGHS.FourColor
