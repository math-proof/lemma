/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem PeriodicPlanarDualPair.PointwiseMacroArrayCertificate.toMacroArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (raw : D.PointwiseMacroArrayCertificate mu) :
    Nonempty (D.MacroArrayCertificate mu) := by
  let q := sheffieldMacroArrayCoordinates raw.B raw.T
    raw.a0 raw.b0 raw.c0 raw.d0
  let horizontal : Nat → Nat → Real := fun k n ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (q n (k + 1)).1 (q n (k + 1)).2.1
      ((q n (k + 1)).2.2.1 + 4 * raw.B)
      ((q n (k + 1)).2.2.2 - 4 * raw.B))
  let primal : Nat → Nat → Real := fun k n ↦ max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (q n k).1 (q n k).2.1
      ((q n k).2.2.1 + 4 * raw.B) ((q n k).2.2.2 - 4 * raw.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (q n k).1 (q n k).2.1 ((q n k).2.2.1 + 4 * raw.B)
      ((q n k).2.2.2 - 4 * raw.B + (raw.T + 4 * raw.B : Nat))))
  let dual : Nat → Nat → Real := fun k n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        ((q n k).1 + 4 * raw.B) ((q n k).2.1 - 4 * raw.B)
        ((q n k).2.2.1) ((q n k).2.2.2)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        ((q n k).1) ((q n k).2.1
        ) ((q n k).2.2.1 + 4 * raw.B) ((q n k).2.2.2 - 4 * raw.B)))
  let combined : Nat → Nat → Real := fun k n ↦
    min (horizontal k n) (min (primal k n) (dual k n))
  have hhorizontal (k : Nat) : Tendsto (horizontal k) atTop (nhds 1) := by
    simpa only [horizontal, q] using raw.horizontalLevel k
  have hprimal (k : Nat) : Tendsto (primal k) atTop (nhds 1) := by
    simpa only [primal, q] using raw.primalLevel k
  have hdual (k : Nat) : Tendsto (dual k) atTop (nhds 1) := by
    simpa only [dual, q] using raw.dualLevel k
  have hcombined (k : Nat) : Tendsto (combined k) atTop (nhds 1) := by
    simpa only [combined, min_self] using
      (hhorizontal k).min ((hprimal k).min (hdual k))
  have hcombinedLe (k n : Nat) : combined k n ≤ 1 := by
    exact (min_le_left _ _).trans measureReal_le_one
  obtain ⟨index, hindex, huniform⟩ :=
    exists_cofinalIndex_uniform_tendsto_one_below_diagonal
      combined hcombined hcombinedLe
  have hindexTop : Tendsto index atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hindex n)
  let K : Nat → Nat := fun n ↦ n.pred
  let a0 : Nat → Real := fun n ↦ raw.a0 (index n)
  let b0 : Nat → Real := fun n ↦ raw.b0 (index n)
  let c0 : Nat → Real := fun n ↦ raw.c0 (index n)
  let d0 : Nat → Real := fun n ↦ raw.d0 (index n)
  let q' := sheffieldMacroArrayCoordinates raw.B raw.T a0 b0 c0 d0
  have hq (n k : Nat) : q' n k = q (index n) k := rfl
  have hcomponentLimit (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ combined (k n) (index n)) atTop (nhds 1) :=
    huniform k hk
  have hhorizontalOfCombined (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ horizontal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n ↦ (min_le_left _ _)) (fun _ ↦ measureReal_le_one)
  have hprimalOfCombined (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ primal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n ↦ (min_le_right _ _).trans (min_le_left _ _))
      (fun _ ↦ max_le measureReal_le_one measureReal_le_one)
  have hdualOfCombined (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ dual (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n ↦ (min_le_right _ _).trans (min_le_right _ _))
      (fun _ ↦ max_le measureReal_le_one measureReal_le_one)
  refine ⟨{
    B := raw.B
    T := raw.T
    Bpos := raw.Bpos
    increment := raw.increment
    primalArcBound := raw.primalArcBound
    dualArcBound := raw.dualArcBound
    a0 := a0
    b0 := b0
    c0 := c0
    d0 := d0
    K := K
    spanX0 := fun n ↦ raw.spanX0 (index n)
    spanY0 := fun n ↦ raw.spanY0 (index n)
    verticalStart := raw.verticalStart.comp hindexTop
    horizontalEnd := ?_
    primalAdjacent := ?_
    dualLevels := ?_ }⟩
  · dsimp only
    have hK : ∀ n, K n < n + 1 := by
      intro n
      dsimp only [K]
      exact (Nat.pred_le n).trans_lt (Nat.lt_succ_self n)
    have hlim := hhorizontalOfCombined K hK
    simpa only [horizontal, q', hq] using hlim
  · dsimp only
    intro k hk
    have hk' : ∀ n, k n < n + 1 := by
      intro n
      have hkn := hk n
      dsimp only [K] at hkn
      exact hkn.trans_le (Nat.succ_le_succ (Nat.pred_le n))
    have hlim := hprimalOfCombined k hk'
    simpa only [primal, q', hq] using hlim
  · dsimp only
    intro k hk
    let k' : Nat → Nat := fun n ↦ if n = 0 then 0 else k n
    have hk' : ∀ n, k' n < n + 1 := by
      intro n
      by_cases hn : n = 0
      · simp [k', hn]
      · have hkn := hk n
        dsimp only [K] at hkn
        have hp : n.pred + 1 = n := by
          cases n with
          | zero => exact (hn rfl).elim
          | succ m => rfl
        rw [hp] at hkn
        simp only [k', hn, if_neg]
        exact Nat.lt_succ_of_le hkn
    have hlim := hdualOfCombined k' hk'
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    simpa [dual, q', hq, k', hn0]


end StatMech.FK.PeriodicPlanar
