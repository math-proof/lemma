/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaBalancedComponentSelector_sources_general
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    StatMech.Sharpness.RandomCurrent.sources e
          ((lpReplicaBalancedComponentSelector G sites m tag).filter
            fun c => (tag c).2 = false) =
        lpReplicaBalancedComponentBoundary G sites m A B tag ∧
      StatMech.Sharpness.RandomCurrent.sources e
          ((lpReplicaBalancedComponentSelector G sites m tag).filter
            fun c => (tag c).2 = true) = ∅ := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  let C0 := edgeComponent e K0
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let C1 := edgeComponent e K1
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hC0 : C0 ⊆ K0 := by
    intro c hc
    change c ∈ edgeComponent e K0 lpReplicaCurrentGhost1 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hC1 : C1 ⊆ K1 := by
    intro c hc
    change c ∈ edgeComponent e K1 lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrows : Disjoint K0 K1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [K0, K1, lpReplicaRowCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at hc0 hc1
    exact Bool.false_ne_true (hc0.symm.trans hc1)
  have hcomponents : Disjoint C0 C1 := hrows.mono hC0 hC1
  have hinter (current : Bool) : Disjoint
      (lpReplicaCurrentCopies G sites m tag false current ∩ C0)
      (lpReplicaCurrentCopies G sites m tag true current ∩ C1) :=
    hcomponents.mono Finset.inter_subset_right Finset.inter_subset_right
  have hcurrent0 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag false current ⊆ K0 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag false current
  have hcurrent1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ⊆ K1 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag true current
  constructor
  · rw [lpReplicaBalancedComponentSelector_filter G sites m tag false,
      sources_union_of_disjoint (hinter false),
      sources_inter_edgeComponent (hcurrent0 false),
      sources_inter_edgeComponent (hcurrent1 false),
      hgate.1, hgate.2.2.2.1]
    rfl
  · rw [lpReplicaBalancedComponentSelector_filter G sites m tag true,
      sources_union_of_disjoint (hinter true),
      sources_inter_edgeComponent (hcurrent0 true),
      sources_inter_edgeComponent (hcurrent1 true),
      hgate.2.1, hgate.2.2.2.2.1]
    simp


theorem lpReplicaBalancedComponentSelector_rowCurrentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let P := lpReplicaBalancedComponentSelector G sites m tag
    let X := lpReplicaBalancedComponentBoundary G sites m B ∅ tag
    StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag false false ∩ P) = X ∧
      StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag true false ∩ P) = ∅ ∧
      StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag false true ∩ P) = ∅ ∧
      StatMech.Sharpness.RandomCurrent.sources e
        (lpReplicaCurrentCopies G sites m tag true true ∩ P) = ∅ := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  let C0 := edgeComponent e K0
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let C1 := edgeComponent e K1
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hC0 : C0 ⊆ K0 := by
    intro c hc
    change c ∈ edgeComponent e K0 lpReplicaCurrentGhost1 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hC1 : C1 ⊆ K1 := by
    intro c hc
    change c ∈ edgeComponent e K1 lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrow0 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag false current ∩ (C0 ∪ C1) =
        lpReplicaCurrentCopies G sites m tag false current ∩ C0 := by
    ext c
    have hc1 := @hC1 c
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hc, hc0 | hc1'⟩
      · exact ⟨hc, hc0⟩
      · have htag0 := hc
        have htag1 := hc1 hc1'
        simp only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag0
        simp only [K1, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag1
        exact False.elim (Bool.false_ne_true
          ((congrArg Prod.fst htag0).symm.trans htag1))
    · exact fun hc => ⟨hc.1, Or.inl hc.2⟩
  have hrow1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ∩ (C0 ∪ C1) =
        lpReplicaCurrentCopies G sites m tag true current ∩ C1 := by
    ext c
    have hc0 := @hC0 c
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hc, hc0' | hc1⟩
      · have htag1 := hc
        have htag0 := hc0 hc0'
        simp only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag1
        simp only [K0, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] at htag0
        exact False.elim (Bool.false_ne_true
          (htag0.symm.trans (congrArg Prod.fst htag1)))
      · exact ⟨hc, hc1⟩
    · exact fun hc => ⟨hc.1, Or.inr hc.2⟩
  have hcurrent0 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag false current ⊆ K0 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag false current
  have hcurrent1 (current : Bool) :
      lpReplicaCurrentCopies G sites m tag true current ⊆ K1 :=
    lpReplicaCurrentCopies_subset_rowCopies G sites m tag true current
  change StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag false false ∩ (C0 ∪ C1)) = _ ∧
    StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag true false ∩ (C0 ∪ C1)) = _ ∧
    StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag false true ∩ (C0 ∪ C1)) = _ ∧
    StatMech.Sharpness.RandomCurrent.sources e
      (lpReplicaCurrentCopies G sites m tag true true ∩ (C0 ∪ C1)) = _
  rw [hrow0 false, hrow1 false, hrow0 true, hrow1 true,
    sources_inter_edgeComponent (hcurrent0 false),
    sources_inter_edgeComponent (hcurrent1 false),
    sources_inter_edgeComponent (hcurrent0 true),
    sources_inter_edgeComponent (hcurrent1 true),
    hgate.1, hgate.2.2.2.1, hgate.2.1, hgate.2.2.2.2.1]
  simp [lpReplicaBalancedComponentBoundary, K0, K1]
  dsimp only [e]
  ext x
  simp [Finset.mem_symmDiff]


theorem lpReplicaBalancedComponentSelector_disconnects_general
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    let moved := lpReplicaToggleRows G sites m
      (lpReplicaBalancedComponentSelector G sites m tag) tag
    (¬ StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m moved false)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧
      ¬ StatMech.Sharpness.RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m moved true)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaRowCopies G sites m tag false
  let K1 := lpReplicaRowCopies G sites m tag true
  let C0 := edgeComponent e K0
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
  let C1 := edgeComponent e K1
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hC0 : C0 ⊆ K0 := by
    intro c hc
    change c ∈ edgeComponent e K0 lpReplicaCurrentGhost1 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hC1 : C1 ⊆ K1 := by
    intro c hc
    change c ∈ edgeComponent e K1 lpReplicaCurrentGhost0 at hc
    rw [edgeComponent, Finset.mem_filter] at hc
    exact hc.1
  have hrows : Disjoint K0 K1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [K0, K1, lpReplicaRowCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at hc0 hc1
    exact Bool.false_ne_true (hc0.symm.trans hc1)
  have hrow0 :
      lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m
            (lpReplicaBalancedComponentSelector G sites m tag) tag) false =
        exchangeFirstRow e K0 K1
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
    rw [lpReplicaRowCopies_toggle]
    change K0 ∆ (C0 ∪ C1) = _
    rw [symmDiff_componentExchange_first hC0 hC1 hrows]
    rfl
  have hrow1 :
      lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m
            (lpReplicaBalancedComponentSelector G sites m tag) tag) true =
        exchangeSecondRow e K0 K1
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
    rw [lpReplicaRowCopies_toggle]
    change K1 ∆ (C0 ∪ C1) = _
    rw [symmDiff_componentExchange_second hC0 hC1 hrows]
    rfl
  rw [hrow0, hrow1]
  exact componentExchange_disconnects
    (show (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
      lpReplicaCurrentGhost1 by
        simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])
    hgate.2.2.1 hgate.2.2.2.2.2


theorem lpReplicaRowGate_balancedComponentExchange_general
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    let D := lpReplicaBalancedComponentBoundary G sites m A B tag
    LPReplicaRowGate G sites m (A ∆ D) (B ∆ D)
      (lpReplicaToggleRows G sites m
        (lpReplicaBalancedComponentSelector G sites m tag) tag) := by
  dsimp only
  have hsources := lpReplicaBalancedComponentSelector_sources_general
    G sites m A B tag hgate
  have hdisc := lpReplicaBalancedComponentSelector_disconnects_general
    G sites m A B tag hgate
  have h := lpReplicaRowGate_toggle G sites m A B tag
    (lpReplicaBalancedComponentSelector G sites m tag) hgate hsources.2
    hdisc.1 hdisc.2
  dsimp only at h
  rw [hsources.1] at h
  exact h


end
end StatMech.Ising
