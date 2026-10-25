/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaBalancedComponentSelector_filter
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (current : Bool) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K0 := lpReplicaRowCopies G sites m tag false
    let K1 := lpReplicaRowCopies G sites m tag true
    let C0 := edgeComponent e K0
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
    let C1 := edgeComponent e K1
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    (lpReplicaBalancedComponentSelector G sites m tag).filter
        (fun c => (tag c).2 = current) =
      (lpReplicaCurrentCopies G sites m tag false current ∩ C0) ∪
        (lpReplicaCurrentCopies G sites m tag true current ∩ C1) := by
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
  change (C0 ∪ C1).filter (fun c => (tag c).2 = current) = _
  ext c
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨hc0 | hc1, hcurrent⟩
    · left
      refine ⟨?_, hc0⟩
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hrow : (tag c).1 = false := by
        have hcK := hC0 hc0
        simpa only [K0, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using hcK
      exact Prod.ext hrow hcurrent
    · right
      refine ⟨?_, hc1⟩
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      have hrow : (tag c).1 = true := by
        have hcK := hC1 hc1
        simpa only [K1, lpReplicaRowCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using hcK
      exact Prod.ext hrow hcurrent
  · rintro (⟨hc, hc0⟩ | ⟨hc, hc1⟩)
    · refine ⟨Or.inl hc0, ?_⟩
      have htag := hc
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] at htag
      exact congrArg Prod.snd htag
    · refine ⟨Or.inr hc1, ?_⟩
      have htag := hc
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] at htag
      exact congrArg Prod.snd htag


theorem lpReplicaBalancedComponentSelector_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag) :
    let e := endsM (lpReplicaCurrentGraph G sites) m
    let K0 := lpReplicaRowCopies G sites m tag false
    let C0 := StatMech.Sharpness.RandomCurrent.compOf e K0
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V)
    StatMech.Sharpness.RandomCurrent.sources e
          ((lpReplicaBalancedComponentSelector G sites m tag).filter
            fun c => (tag c).2 = false) = B ∩ C0 ∧
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
    simp [K0]
  · rw [lpReplicaBalancedComponentSelector_filter G sites m tag true,
      sources_union_of_disjoint (hinter true),
      sources_inter_edgeComponent (hcurrent0 true),
      sources_inter_edgeComponent (hcurrent1 true),
      hgate.2.1, hgate.2.2.2.2.1]
    simp


theorem lpReplicaBalancedComponentSelector_disconnects
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag) :
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


end
end StatMech.Ising
