/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part21
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem rightRowData_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (rightRowData ends m j k l zero) =
      ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  classical
  calc
    Fintype.card (rightRowData ends m j k l zero) =
        ∑ K : rightRowSupportIndex ends m j k l zero, rowSupportWeight ends m K.1 := by
      change Fintype.card (Σ K : rightRowSupportIndex ends m j k l zero,
        boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) ∅) = _
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro K _
      rw [Fintype.card_prod]
      obtain ⟨P, hPK, hPsrc⟩ := K.2.2.2.1
      have hKA : boundarySector ends K.1 {j, k} := ⟨P, hPK, hPsrc⟩
      have hL0 : boundarySector ends (m \ K.1) ∅ :=
        ⟨m \ K.1, Finset.Subset.rfl, K.2.2.2.2.1⟩
      rw [boundarySector_card_eq_cycle ends K.1 {j, k} hKA]
      rfl
    _ = ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
      symm
      exact Finset.sum_subtype _ (fun K => by simp [rightRowSupports]) _

theorem rightFiber_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (rightFiber ends m {j, k} {k, l} k zero) =
      ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  rw [Fintype.card_congr (rightFiberEquivRowData ends m j k l zero),
    rightRowData_card_eq_weightedSum]

theorem GrahamFiberMinor_of_weightedRowMinor (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (h : GrahamWeightedRowMinor ends m j k l zero) :
    GrahamFiberMinor ends m j k l zero := by
  rw [GrahamFiberMinor, leftFiber_card_eq_weightedSum, rightFiber_card_eq_weightedSum]
  exact h

theorem GrahamFiberMinor_iff_weightedRowMinor (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    GrahamFiberMinor ends m j k l zero ↔ GrahamWeightedRowMinor ends m j k l zero := by
  rw [GrahamFiberMinor, GrahamWeightedRowMinor, leftFiber_card_eq_weightedSum,
    rightFiber_card_eq_weightedSum]


theorem componentExchange_maps_leftRowSupport {ends : ι → Sym2 W} {m K : Finset ι}
    {j k l zero : W} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag) (hKm : K ⊆ m)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hleft : LeftRowSupport ends m j k l zero K) :
    let K' := exchangeFirstRow ends K (m \ K) k zero
    K' ⊆ m ∧ RightRowSupport ends m j k l zero K' := by
  classical
  let L := m \ K
  let K' := exchangeFirstRow ends K L k zero
  let L' := exchangeSecondRow ends K L k zero
  have hLsub : L ⊆ m := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hKL : Disjoint K L := by
    rw [Finset.disjoint_left]
    intro i hiK hiL
    exact (Finset.mem_sdiff.mp hiL).2 hiK
  have hE0sub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1sub : edgeComponent ends L k ⊆ L := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hK'sub : K' ⊆ m := by
    intro i hi
    dsimp only [K', exchangeFirstRow] at hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hKm (Finset.mem_sdiff.mp hi).1
    · exact hLsub (hE1sub hi)
  have hcompl : m \ K' = L' := by
    ext i
    have hE0 := @hE0sub i
    have hE1 := @hE1sub i
    have hKi := @hKm i
    simp only [K', L', exchangeFirstRow, exchangeSecondRow, Finset.mem_sdiff,
      Finset.mem_union]
    dsimp only [L] at hE1 ⊢
    by_cases hiK : i ∈ K <;> by_cases him : i ∈ m <;>
      by_cases hiE0 : i ∈ edgeComponent ends K zero <;>
        by_cases hiE1 : i ∈ edgeComponent ends (m \ K) k <;>
          simp [hiK, him, hiE0, hiE1] at hE0 hE1 hKi ⊢
  have hjkConn : Sharpness.RandomCurrent.connK ends K j k :=
    Walls.gc6_pairingPath_abstract ends K K (fun i hi => hloop i (hKm hi))
      Finset.Subset.rfl hleft.1 hjk
  have hE0src : Sharpness.RandomCurrent.sources ends (edgeComponent ends K zero) = ∅ := by
    rw [sources_edgeComponent, hleft.1]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
    rw [Sharpness.RandomCurrent.mem_compOf] at hcomp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hleft.2.2.1
        (Sharpness.RandomCurrent.connK_symm ends K (hcomp.trans hjkConn))
    · exact hleft.2.2.1 (Sharpness.RandomCurrent.connK_symm ends K hcomp)
  have hPsrc : Sharpness.RandomCurrent.sources ends (K \ edgeComponent ends K zero) =
      {j, k} := by
    rw [sources_sdiff_of_subset hE0sub, hleft.1, hE0src]
    simp
  have hPsub : K \ edgeComponent ends K zero ⊆ K' := by
    intro i hi
    dsimp only [K', exchangeFirstRow]
    exact Finset.mem_union_left _ hi
  have hbound := componentExchange_boundaries
    (K := K) (L := L) (j := j) (k := k) (l := l) (zero := zero)
    (fun i hi => hloop i (hKm hi)) (fun i hi => hloop i (hLsub hi)) hKL hjk hkl
    hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2
  have hdisc := componentExchange_disconnects hk0 hleft.2.2.1 hleft.2.2.2
  dsimp only
  refine ⟨hK'sub, ?_⟩
  unfold RightRowSupport
  change Sharpness.RandomCurrent.sources ends K' = {j, k} ∆ {k, l} ∧
    (∃ P, P ⊆ K' ∧ Sharpness.RandomCurrent.sources ends P = {j, k}) ∧
    Sharpness.RandomCurrent.sources ends (m \ K') = ∅ ∧
    ¬ Sharpness.RandomCurrent.connK ends K' k zero ∧
    ¬ Sharpness.RandomCurrent.connK ends (m \ K') k zero
  rw [hcompl]
  exact ⟨hbound.1, ⟨K \ edgeComponent ends K zero, hPsub, hPsrc⟩,
    hbound.2, hdisc.1, hdisc.2⟩


theorem GrahamFiberMinor_of_balancedSelector (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (σ : (↑m → Fin 4) → Finset ι × Finset ι)
    (hvalid : ∀ c, LeftPattern ends m {j, k} {k, l} k zero c →
      let X := (σ c).1
      let Y := (σ c).2
      X ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧
      Y ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧
      Sharpness.RandomCurrent.sources ends X = {k, l} ∧
      Sharpness.RandomCurrent.sources ends Y = ∅ ∧
      RowsDisconnect ends m (balancedSwap m X Y c) k zero)
    (hequiv : ∀ c,
      σ (balancedSwap m (σ c).1 (σ c).2 c) = σ c) :
    GrahamFiberMinor ends m j k l zero := by
  classical
  let f : leftFiber ends m {j, k} {k, l} k zero →
      rightFiber ends m {j, k} {k, l} k zero := fun c =>
    ⟨balancedSwap m (σ c.1).1 (σ c.1).2 c.1, by
      rcases hvalid c.1 c.2 with ⟨hX, hY, hsrcX, hsrcY, hdisc⟩
      exact rightPattern_of_balancedTransfer c.2 hX hY hsrcX hsrcY hdisc⟩
  apply Fintype.card_le_of_injective f
  intro c d hcd
  apply Subtype.ext
  have himage : balancedSwap m (σ c.1).1 (σ c.1).2 c.1 =
      balancedSwap m (σ d.1).1 (σ d.1).2 d.1 := congrArg Subtype.val hcd
  have hsigma : σ c.1 = σ d.1 := by
    rw [← hequiv c.1, ← hequiv d.1, himage]
  calc
    c.1 = balancedSwap m (σ c.1).1 (σ c.1).2
        (balancedSwap m (σ c.1).1 (σ c.1).2 c.1) :=
      (balancedSwap_involutive m (σ c.1).1 (σ c.1).2 c.1).symm
    _ = balancedSwap m (σ d.1).1 (σ d.1).2
        (balancedSwap m (σ d.1).1 (σ d.1).2 d.1) := by
      have himage' : balancedSwap m (σ d.1).1 (σ d.1).2 c.1 =
          balancedSwap m (σ d.1).1 (σ d.1).2 d.1 := by
        simpa [hsigma] using himage
      rw [hsigma]
      exact congrArg (balancedSwap m (σ d.1).1 (σ d.1).2) himage'
    _ = d.1 := balancedSwap_involutive m (σ d.1).1 (σ d.1).2 d.1


theorem FiberMinorCandidate_of_total_disconnected (ends : ι → Sym2 W) (m : Finset ι)
    (A B : Finset W) (u v : W) (hdisc : ¬ Sharpness.RandomCurrent.connK ends m u v) :
    FiberMinorCandidate ends m A B u v := by
  classical
  have hrows : ∀ c : ↑m → Fin 4, RowsDisconnect ends m c u v := by
    intro c
    constructor <;> intro hc
    · exact hdisc (connK_mono
        (Finset.union_subset (colorClass_subset m c 0) (colorClass_subset m c 1)) hc)
    · exact hdisc (connK_mono
        (Finset.union_subset (colorClass_subset m c 2) (colorClass_subset m c 3)) hc)
  let f : leftFiber ends m A B u v → rightFiber ends m A B u v := fun c =>
    ⟨middleSwap m c.1, by
      rcases c.2 with ⟨h0, h1, h2, h3, _⟩
      unfold RightPattern
      have e0 : colorClass m (middleSwap m c.1) 0 = colorClass m c.1 0 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 0
      have e1 : colorClass m (middleSwap m c.1) 1 = colorClass m c.1 2 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 1
      have e2 : colorClass m (middleSwap m c.1) 2 = colorClass m c.1 1 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 2
      have e3 : colorClass m (middleSwap m c.1) 3 = colorClass m c.1 3 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 3
      refine ⟨?_, ?_, ?_, ?_, hrows _⟩
      · rw [e0]; exact h0
      · rw [e1]; exact h2
      · rw [e2]; exact h1
      · rw [e3]; exact h3⟩
  apply Fintype.card_le_of_injective f
  intro c d hcd
  apply Subtype.ext
  have hfun : middleSwap m c.1 = middleSwap m d.1 := congrArg Subtype.val hcd
  calc
    c.1 = middleSwap m (middleSwap m c.1) := (middleSwap_involutive m c.1).symm
    _ = middleSwap m (middleSwap m d.1) := congrArg (middleSwap m) hfun
    _ = d.1 := middleSwap_involutive m d.1


theorem GrahamFiberMinor_of_total_disconnected (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (hdisc : ¬ Sharpness.RandomCurrent.connK ends m k zero) :
    GrahamFiberMinor ends m j k l zero :=
  FiberMinorCandidate_of_total_disconnected ends m {j, k} {k, l} k zero hdisc

end FourColor
end GrahamGHS
end StatMech
