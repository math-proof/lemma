/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part9
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shbK4Path023_support
    (E : Finset shbK4Edge) (h02 : shbK4Edge.e02 ∈ E)
    (h23 : shbK4Edge.e23 ∈ E) :
    (shbK4Path023 E h02 h23).1.support = [(0 : Fin 4), 2, 3] := by
  simp [shbK4Path023]

theorem shbK4_isBackboneOf_iff_pathSupported
    (E : Finset shbK4Edge) (n : Current (Fin 4)) {x y : Fin 4}
    (p : (shbK4Graph E).Path x y) :
    shb_IsBackboneOf (shbK4Graph E) n x y p ↔
      shbK4PathSupported (shbK4OddSupport E n) p := by
  constructor
  · intro hp e he
    have heG := p.1.edges_subset_edgeSet he
    rw [shbK4Graph_mem_edgeSet_iff] at heG
    obtain ⟨k, hkE, hcode⟩ := Finset.mem_image.mp heG
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, hcode⟩
    apply Finset.mem_filter.mpr
    refine ⟨hkE, ?_⟩
    rw [hcode]
    exact hp e he
  · intro hp e he
    obtain ⟨k, hkA, hcode⟩ := Finset.mem_image.mp (hp e he)
    rw [← hcode]
    exact (Finset.mem_filter.mp hkA).2


theorem shbK4_selectsDirect03_iff_realized_minimal
    (E A : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E) (hAE : A ⊆ E) :
    shbK4SelectsDirect03 A ↔
      shbK4Boundary A = {0, 3} ∧
        shbK4PathSupported A (shbK4DirectPath E h03) ∧
        ∀ q : (shbK4Graph E).Path (0 : Fin 4) 3,
          q.1.support < (shbK4DirectPath E h03).1.support →
            ¬ shbK4PathSupported A q := by
  constructor
  · intro hselect
    unfold shbK4SelectsDirect03 at hselect
    rcases hselect with ⟨hboundary, h03A, h013, h0123, h0213, h023⟩
    refine ⟨hboundary, (shbK4DirectPath_supported_iff E A h03).2 h03A, ?_⟩
    intro q hlt hsupported
    rw [shbK4DirectPath_support] at hlt
    have hfirst : q.1.support.head? = some 0 := by
      rw [← q.1.cons_tail_support]
      rfl
    have hlast : q.1.support.getLast? = some 3 := by
      rw [List.getLast?_eq_getLast_of_ne_nil q.1.support_ne_nil,
        q.1.getLast_support]
    rcases shbK4_support_lt_direct_classification q.1.support
        q.2.support_nodup hfirst hlast hlt with hq | hq | hq | hq
    · exact h0123 ((shbK4PathSupported_0123_iff q hq).1 hsupported)
    · exact h013 ((shbK4PathSupported_013_iff q hq).1 hsupported)
    · exact h0213 ((shbK4PathSupported_0213_iff q hq).1 hsupported)
    · exact h023 ((shbK4PathSupported_023_iff q hq).1 hsupported)
  · rintro ⟨hboundary, hsupported, hminimal⟩
    unfold shbK4SelectsDirect03
    refine ⟨hboundary, (shbK4DirectPath_supported_iff E A h03).1 hsupported,
      ?_, ?_, ?_, ?_⟩
    · intro hsubset
      have h01A : shbK4Edge.e01 ∈ A := hsubset (by simp)
      have h13A : shbK4Edge.e13 ∈ A := hsubset (by simp)
      let q := shbK4Path013 E (hAE h01A) (hAE h13A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_013_iff q (by simp [q])).2 hsubset
    · intro hsubset
      have h01A : shbK4Edge.e01 ∈ A := hsubset (by simp)
      have h12A : shbK4Edge.e12 ∈ A := hsubset (by simp)
      have h23A : shbK4Edge.e23 ∈ A := hsubset (by simp)
      let q := shbK4Path0123 E (hAE h01A) (hAE h12A) (hAE h23A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_0123_iff q (by simp [q])).2 hsubset
    · intro hsubset
      have h02A : shbK4Edge.e02 ∈ A := hsubset (by simp)
      have h12A : shbK4Edge.e12 ∈ A := hsubset (by simp)
      have h13A : shbK4Edge.e13 ∈ A := hsubset (by simp)
      let q := shbK4Path0213 E (hAE h02A) (hAE h12A) (hAE h13A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_0213_iff q (by simp [q])).2 hsubset
    · intro hsubset
      have h02A : shbK4Edge.e02 ∈ A := hsubset (by simp)
      have h23A : shbK4Edge.e23 ∈ A := hsubset (by simp)
      let q := shbK4Path023 E (hAE h02A) (hAE h23A)
      apply hminimal q
      · simp [q]
        decide
      · exact (shbK4PathSupported_023_iff q (by simp [q])).2 hsubset


theorem shb_backboneSelectSupport_eq_some_iff
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (x y : V) (p : G.Path x y) :
    shb_backboneSelectSupport G n x y = some p ↔
      shb_IsBackboneOf G n x y p ∧
        ∀ q : G.Path x y, q.1.support < p.1.support →
          ¬ shb_IsBackboneOf G n x y q := by
  letI : LinearOrder (G.Path x y) := shb_supportPathOrder G x y
  constructor
  · intro hsel
    unfold shb_backboneSelectSupport at hsel
    split at hsel
    · rename_i hne
      have hmin : (shb_backboneSet G n x y).min' hne = p :=
        Option.some.inj hsel
      have hp : p ∈ shb_backboneSet G n x y := by
        rw [← hmin]
        exact Finset.min'_mem _ _
      refine ⟨(shb_mem_backboneSet G n x y p).mp hp, ?_⟩
      intro q hqp hq
      have hqmem : q ∈ shb_backboneSet G n x y :=
        (shb_mem_backboneSet G n x y q).mpr hq
      have hle : (shb_backboneSet G n x y).min' hne ≤ q :=
        Finset.min'_le _ _ hqmem
      rw [hmin] at hle
      exact (not_lt_of_ge hle) hqp
    · simp at hsel
  · rintro ⟨hp, hbefore⟩
    have hpmem : p ∈ shb_backboneSet G n x y :=
      (shb_mem_backboneSet G n x y p).mpr hp
    have hne : (shb_backboneSet G n x y).Nonempty := ⟨p, hpmem⟩
    unfold shb_backboneSelectSupport
    rw [dif_pos hne]
    apply congrArg some
    apply le_antisymm
    · exact Finset.min'_le _ _ hpmem
    · apply not_lt.mp
      intro hlt
      exact hbefore _ hlt
        ((shb_mem_backboneSet G n x y _).mp (Finset.min'_mem _ _))


theorem shbK4_source_selector_fiber_iff
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (n : Current (Fin 4)) :
    (sources (shbK4Graph E) n = {(0 : Fin 4), 3} ∧
        shb_backboneSelectSupport (shbK4Graph E) n 0 3 =
          some (shbK4DirectPath E h03)) ↔
      shbK4SelectsDirect03 (shbK4OddSupport E n) := by
  rw [shbK4_selectsDirect03_iff_realized_minimal E
    (shbK4OddSupport E n) h03 (Finset.filter_subset _ _)]
  rw [shb_backboneSelectSupport_eq_some_iff]
  rw [shbK4_sources_eq_boundary]
  simp_rw [shbK4_isBackboneOf_iff_pathSupported]


theorem shbK4Graph_mono {E F : Finset shbK4Edge} (hEF : E ⊆ F) :
    shbK4Graph E ≤ shbK4Graph F := by
  intro x y hxy
  rw [shbK4Graph, SimpleGraph.fromEdgeSet_adj] at hxy ⊢
  refine ⟨?_, hxy.2⟩
  obtain ⟨k, hkE, hk⟩ := Finset.mem_image.mp hxy.1
  exact Finset.mem_image.mpr ⟨k, hEF hkE, hk⟩

theorem shbK4H_subset_shbK4G : shbK4H ⊆ shbK4G := by
  exact Finset.ssubset_iff_subset_ne.mp shbK4H_ssubset_shbK4G |>.1


theorem shbK4DirectPath_mapLe :
    shb_pathMapLe (shbK4Graph_mono shbK4H_subset_shbK4G)
        (shbK4DirectPath shbK4H (by decide)) =
      shbK4DirectPath shbK4G (by decide) := by
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  simp only [shb_pathMapLe, SimpleGraph.Walk.support_mapLe_eq_support,
    shbK4DirectPath_support]


theorem shbK4_ofEdgeFun_source_selector_fiber_iff
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (m : (shbK4Graph E).edgeFinset → ℕ) :
    (sources (shbK4Graph E) (ofEdgeFun (shbK4Graph E) m) =
          {(0 : Fin 4), 3} ∧
        shb_backboneSelectSupport (shbK4Graph E)
            (ofEdgeFun (shbK4Graph E) m) 0 3 =
          some (shbK4DirectPath E h03)) ↔
      shbK4SelectsDirect03
        (shbK4OddSupport E (ofEdgeFun (shbK4Graph E) m)) :=
  shbK4_source_selector_fiber_iff E h03 _


theorem shbK4_weight_ofEdgeFun_one
    (E : Finset shbK4Edge) (x : ℝ)
    (m : (shbK4Graph E).edgeFinset → ℕ) :
    weight (shbK4Graph E) x (fun _ ↦ 1)
        (ofEdgeFun (shbK4Graph E) m) =
      ∏ k : ↑E,
        x ^ (m (shbK4GraphEdgeEquiv E k)) /
          (m (shbK4GraphEdgeEquiv E k)).factorial := by
  rw [weight_ofEdgeFun]
  simp only [mul_one]
  exact (Equiv.prod_comp (shbK4GraphEdgeEquiv E)
    (fun e : (shbK4Graph E).edgeFinset ↦
      x ^ (m e) / (m e).factorial)).symm

end StatMech.Sharpness
