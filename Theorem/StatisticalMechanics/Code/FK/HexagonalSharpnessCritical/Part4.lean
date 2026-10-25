/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part4
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem hexagonalRootFrame_adj (u v : HexVertex) :
    hexagonalGraph.Adj (hexagonalRootFrame u) (hexagonalRootFrame v) ↔
      hexagonalGraph.Adj u v := by
  by_cases h : hexagonal.root.2
  · simpa [hexagonalRootFrame, h] using (hexagonalReflect_adj u v).symm
  · simp [hexagonalRootFrame, h]

theorem hexagonalRootFrame_coord_mem_box_iff (n : Nat) (v : HexVertex) :
    (hexagonalRootFrame v).1 ∈ box 2 n ↔ v.1 ∈ box 2 n := by
  by_cases h : hexagonal.root.2
  · constructor <;> intro hv
    · have := site_neg_mem_box hv
      simpa [hexagonalRootFrame, h, hexagonalReflect] using this
    · simpa [hexagonalRootFrame, h, hexagonalReflect] using site_neg_mem_box hv
  · simp [hexagonalRootFrame, h]

theorem hexagonalRootFrame_mem_orbitBox_iff (n : Nat) (v : HexVertex) :
    hexagonalRootFrame v ∈ hexagonal.orbitBox n ↔
      v ∈ hexagonal.orbitBox n := by
  rw [hexagonal_mem_orbitBox_iff_box, hexagonal_mem_orbitBox_iff_box]
  exact hexagonalRootFrame_coord_mem_box_iff n v

theorem hexagonalRootFrame_root :
    hexagonalRootFrame hexagonal.root = ((0, false) : HexVertex) := by
  by_cases hcolor : hexagonal.root.2
  · simp [hexagonalRootFrame, hcolor, hexagonalReflect,
      hexagonal_root_coord_eq_zero]
  · rw [show hexagonalRootFrame hexagonal.root = hexagonal.root by
      simp [hexagonalRootFrame, hcolor]]
    apply Prod.ext
    · exact hexagonal_root_coord_eq_zero
    · exact Bool.eq_false_of_not_eq_true hcolor

theorem hexagonal_percolationEvent_subset_innerShell
    (k : Nat) (hk : 1 ≤ k) :
    hexagonal.percolationEvent ⊆
      hexagonal.bufferedCylinder
        (hexagonalTransBufferLevel k hexagonal.root.1)
        (hexagonalBufferedTransShellEvent k hexagonal.root) := by
  intro omega hperc
  have hall : ∀ n, omega ∈ hexagonal.bufferedCylinder n
      (hexagonal.bufferedRootBoundaryEvent n) := by
    have hinter : omega ∈ ⋂ n, hexagonal.bufferedCylinder n
        (hexagonal.bufferedRootBoundaryEvent n) := by
      rw [hexagonal.iInter_bufferedRootBoundaryCylinder]
      exact hperc
    exact Set.mem_iInter.mp hinter
  let L := hexagonalTransBufferLevel k hexagonal.root.1
  obtain ⟨v, hvBoundary, hreach⟩ := hall L
  have hfull := hexagonal.bufferedReachable_full L omega hreach
  change (hexagonal.openSubgraph omega).Reachable hexagonal.root v.1 at hfull
  have hvFar : k ≤ centeredRadius hexagonal.root.1 v.1.1 := by
    by_contra hnot
    have hrad : centeredRadius hexagonal.root.1 v.1.1 ≤ k - 1 := by omega
    have hvbox : v.1.1 ∈ box 2 k := by
      rw [mem_box_iff_siteRadius_le]
      have hvRad : siteRadius v.1.1 ≤ k - 1 := by
        simpa [centeredRadius, hexagonal_root_coord_eq_zero] using hrad
      exact hvRad.trans (Nat.sub_le k 1)
    have hvEarlier : v.1 ∈
        hexagonal.orbitBox (hexagonal.bufferedRadius k) := by
      rw [hexagonal_mem_orbitBox_iff_box]
      exact box_mono 2 (hexagonal.id_le_bufferedRadius k) hvbox
    have hkL : k < L := by
      dsimp [L, hexagonalTransBufferLevel]
      rw [hexagonal_root_coord_eq_zero]
      simp [siteRadius]
      omega
    exact (hexagonal.bufferedBoundary_not_mem_of_lt hkL v hvBoundary) hvEarlier
  exact hexagonal_twoPointEvent_subset_transShell
    k hk hexagonal.root v.1 hvFar hfull

theorem hexagonal_wiredPercolationProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q ≤
      hexagonalOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := hexagonal.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
      hexagonal.percolationEvent ≤
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder
          (hexagonalTransBufferLevel k hexagonal.root.1)
          (hexagonalBufferedTransShellEvent k hexagonal.root)) :=
    measureReal_mono (hexagonal_percolationEvent_subset_innerShell k hk)
      (measure_ne_top _ _)
  rw [show hexagonal.wiredPercolationProbability
      (1 - Real.exp (-beta)) q =
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        hexagonal.percolationEvent by
    simp [PeriodicGraph.wiredPercolationProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (hexagonalBufferedTransShell_infinite_le_theta
      k hk hexagonal.root q beta hq hbeta)


end StatMech.FK.PeriodicPlanar
