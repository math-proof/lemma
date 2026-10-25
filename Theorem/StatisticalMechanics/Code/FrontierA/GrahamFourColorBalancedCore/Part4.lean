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
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part5
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem componentExchange_disconnects {ends : ι → Sym2 W} {K L : Finset ι}
    {k zero : W} (hk0 : k ≠ zero)
    (hK : ¬ Sharpness.RandomCurrent.connK ends K k zero)
    (hL : ¬ Sharpness.RandomCurrent.connK ends L k zero) :
    ¬ Sharpness.RandomCurrent.connK ends (exchangeFirstRow ends K L k zero) k zero ∧
      ¬ Sharpness.RandomCurrent.connK ends (exchangeSecondRow ends K L k zero) k zero := by
  classical
  constructor
  · intro hkzero
    apply (not_connK_of_no_incident hk0.symm ?_)
      (Sharpness.RandomCurrent.connK_symm ends _ hkzero)
    intro i hi hzero
    rw [exchangeFirstRow, Finset.mem_union] at hi
    rcases hi with hi | hi
    · rcases Finset.mem_sdiff.mp hi with ⟨hiK, hin⟩
      exact hin (mem_edgeComponent_of_endpoint hiK hzero)
    · rw [edgeComponent, Finset.mem_filter] at hi
      exact hL (hi.2 zero hzero)
  · apply not_connK_of_no_incident hk0
    intro i hi hk
    rw [exchangeSecondRow, Finset.mem_union] at hi
    rcases hi with hi | hi
    · rcases Finset.mem_sdiff.mp hi with ⟨hiL, hin⟩
      exact hin (mem_edgeComponent_of_endpoint hiL hk)
    · rw [edgeComponent, Finset.mem_filter] at hi
      have hz0k := hi.2 k hk
      exact hK (Sharpness.RandomCurrent.connK_symm ends K hz0k)


theorem componentExchange_boundaries {ends : ι → Sym2 W} {K L : Finset ι}
    {j k l zero : W} (hloopK : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (hloopL : ∀ i ∈ L, ¬ (ends i).IsDiag) (hKL : Disjoint K L)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hsrcK : Sharpness.RandomCurrent.sources ends K = {j, k})
    (hsrcL : Sharpness.RandomCurrent.sources ends L = {k, l})
    (hdiscK : ¬ Sharpness.RandomCurrent.connK ends K k zero)
    (hdiscL : ¬ Sharpness.RandomCurrent.connK ends L k zero) :
    Sharpness.RandomCurrent.sources ends (exchangeFirstRow ends K L k zero) =
        {j, k} ∆ {k, l} ∧
      Sharpness.RandomCurrent.sources ends (exchangeSecondRow ends K L k zero) = ∅ := by
  classical
  have hjkConn : Sharpness.RandomCurrent.connK ends K j k := by
    exact Walls.gc6_pairingPath_abstract ends K K hloopK Finset.Subset.rfl hsrcK hjk
  have hklConn : Sharpness.RandomCurrent.connK ends L k l := by
    exact Walls.gc6_pairingPath_abstract ends L L hloopL Finset.Subset.rfl hsrcL hkl
  have hE0src : Sharpness.RandomCurrent.sources ends (edgeComponent ends K zero) = ∅ := by
    rw [sources_edgeComponent, hsrcK]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
    rw [Sharpness.RandomCurrent.mem_compOf] at hcomp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hdiscK
        (Sharpness.RandomCurrent.connK_symm ends K (hcomp.trans hjkConn))
    · exact hdiscK (Sharpness.RandomCurrent.connK_symm ends K hcomp)
  have hE1src : Sharpness.RandomCurrent.sources ends (edgeComponent ends L k) = {k, l} := by
    rw [sources_edgeComponent, hsrcL]
    apply Finset.inter_eq_left.mpr
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Sharpness.RandomCurrent.mem_compOf]
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hklConn
  have hE0sub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1sub : edgeComponent ends L k ⊆ L := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hdFirst : Disjoint (K \ edgeComponent ends K zero) (edgeComponent ends L k) :=
    hKL.mono Finset.sdiff_subset hE1sub
  have hdSecond : Disjoint (L \ edgeComponent ends L k) (edgeComponent ends K zero) :=
    hKL.symm.mono Finset.sdiff_subset hE0sub
  constructor
  · rw [exchangeFirstRow, sources_union_of_disjoint hdFirst,
      sources_sdiff_of_subset hE0sub, hsrcK, hE0src, hE1src]
    simp
  · rw [exchangeSecondRow, sources_union_of_disjoint hdSecond,
      sources_sdiff_of_subset hE1sub, hsrcL, hE1src, hE0src, symmDiff_self]
    rfl


end FourColor
end GrahamGHS
end StatMech
