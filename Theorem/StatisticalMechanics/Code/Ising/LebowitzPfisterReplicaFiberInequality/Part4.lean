/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateProfileOrbitInequality_of_offdiag
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hpoint : ∀ q i j, i ≠ j ->
      let Si := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
      let Sj := lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
      let T := lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
      lpReplicaProfileOrbitMass G sites beta J hf r ∅ (Si ∆ Sj ∆ T) q <=
        lpReplicaProfileOrbitMass G sites beta J hf r Si (Sj ∆ T) q +
          lpReplicaProfileOrbitMass G sites beta J hf r Sj (Si ∆ T) q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  classical
  let Si : I -> Finset (LPReplicaCurrentVertex V) := fun i =>
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let o := lpReplicaProfileOrbitMass G sites beta J hf r
  intro q
  have hterm (i j : I) :
      (if i = j then 0 else o ∅ (Si i ∆ Si j ∆ T) q) <=
        o (Si i) (Si j ∆ T) q + o (Si j) (Si i ∆ T) q := by
    by_cases hij : i = j
    · rw [if_pos hij]
      exact add_nonneg
        (lpReplicaProfileOrbitMass_nonneg
          G sites beta J hf r hbeta hJ hhf hr (Si i) (Si j ∆ T) q)
        (lpReplicaProfileOrbitMass_nonneg
          G sites beta J hf r hbeta hJ hhf hr (Si j) (Si i ∆ T) q)
    · rw [if_neg hij]
      simpa only [o, Si, T] using hpoint q i j hij
  calc
    (∑ i : I, ∑ j : I, if i = j then 0 else
        o ∅ (Si i ∆ Si j ∆ T) q) <=
        ∑ i : I, ∑ j : I,
          (o (Si i) (Si j ∆ T) q + o (Si j) (Si i ∆ T) q) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = ∑ i : I, ∑ j : I, 2 * o (Si i) (Si j ∆ T) q := by
      simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
      rw [Finset.sum_comm]
      ring

theorem summable_finset_sum_apply
    {X Y : Type*} [DecidableEq X]
    (s : Finset X) (f : X -> Y -> Real)
    (hf : ∀ x ∈ s, Summable (f x)) :
    Summable (fun y => ∑ x ∈ s, f x y) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      exact (hf x (Finset.mem_insert_self x s)).add
        (ih fun y hy => hf y (Finset.mem_insert_of_mem hy))


theorem lpReplicaMatchingDisconn_le_of_profileOrbit
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (horbit : LPReplicaAggregateProfileOrbitInequality
      G sites beta J hf r) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr ∅ ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnTwo H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      2 * lpMatchingDisconnZero H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        lpMatchingDisconnOne H beta Jr
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let Si : I -> Finset (LPReplicaCurrentVertex V) := fun i =>
    lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let dE := sourcePairDisconnSum H beta Jr ∅ ∅
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let a : I -> Real := fun i => sourcePairDisconnSum H beta Jr
    (Si i) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let b : I -> Real := fun i => sourcePairDisconnSum H beta Jr
    (Si i ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let c : I -> I -> Real := fun i j => sourcePairDisconnSum H beta Jr
    (Si i ∆ Si j ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  let o : Finset (LPReplicaCurrentVertex V) ->
      Finset (LPReplicaCurrentVertex V) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real :=
    lpReplicaProfileOrbitMass G sites beta J hf r
  have hOrbitSummable (A B : Finset (LPReplicaCurrentVertex V)) :
      Summable (o A B) :=
    lpReplicaProfileOrbitMass_summable
      G sites beta J hf r hbeta hJ hhf hr A B
  have hprod (A B : Finset (LPReplicaCurrentVertex V)) :
      sourcePairDisconnSum H beta Jr A ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr B ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑' q, o A B q :=
    lpReplica_sourcePairDisconn_mul_eq_tsum_profileOrbitMass
      G sites beta J hf r hbeta hJ hhf hr A B
  rw [lpMatchingDisconnTwo_eq_offDiag H beta Jr
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (by simp
      [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1])]
  unfold lpMatchingDisconnTwoOffDiag lpMatchingDisconnZero lpMatchingDisconnOne
  change dE * (∑ i : I, ∑ j : I, if i = j then 0 else c i j) <=
    2 * (∑ i : I, a i) * ∑ j : I, b j
  rw [show dE * (∑ i : I, ∑ j : I, if i = j then 0 else c i j) =
      ∑ i : I, ∑ j : I, if i = j then 0 else dE * c i j by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all]
  rw [show 2 * (∑ i : I, a i) * ∑ j : I, b j =
      ∑ i : I, ∑ j : I, 2 * (a i * b j) by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring]
  have hleftTerm (i j : I) :
      (if i = j then 0 else dE * c i j) =
        ∑' q, if i = j then 0 else o ∅ (Si i ∆ Si j ∆ T) q := by
    by_cases hij : i = j
    · simp [hij]
    · simp only [if_neg hij]
      simpa only [dE, c] using hprod ∅ (Si i ∆ Si j ∆ T)
  have hrightTerm (i j : I) :
      2 * (a i * b j) = ∑' q, 2 * o (Si i) (Si j ∆ T) q := by
    rw [hprod (Si i) (Si j ∆ T)]
    symm
    exact (hOrbitSummable (Si i) (Si j ∆ T)).tsum_mul_left 2
  simp_rw [hleftTerm, hrightTerm]
  let l : I -> I ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real :=
    fun i j q => if i = j then 0 else o ∅ (Si i ∆ Si j ∆ T) q
  let rr : I -> I ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real :=
    fun i j q => 2 * o (Si i) (Si j ∆ T) q
  have hl (i j : I) : Summable (l i j) := by
    by_cases hij : i = j
    · simp [l, hij]
    · simpa [l, hij] using hOrbitSummable ∅ (Si i ∆ Si j ∆ T)
  have hrr (i j : I) : Summable (rr i j) := by
    exact (hOrbitSummable (Si i) (Si j ∆ T)).mul_left 2
  have hswapL : (∑ i : I, ∑ j : I, ∑' q, l i j q) =
      ∑' q, ∑ i : I, ∑ j : I, l i j q := by
    symm
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum fun j _ => hl i j]
    · intro i _
      exact summable_finset_sum_apply Finset.univ (l i) fun j _ => hl i j
  have hswapR : (∑ i : I, ∑ j : I, ∑' q, rr i j q) =
      ∑' q, ∑ i : I, ∑ j : I, rr i j q := by
    symm
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum fun j _ => hrr i j]
    · intro i _
      exact summable_finset_sum_apply Finset.univ (rr i) fun j _ => hrr i j
  rw [hswapL, hswapR]
  apply Summable.tsum_le_tsum
  · simpa only [l, rr, o, Si, T] using horbit
  · exact summable_finset_sum_apply Finset.univ
      (fun i q => ∑ j : I, l i j q) fun i _ =>
        summable_finset_sum_apply Finset.univ (l i) fun j _ => hl i j
  · exact summable_finset_sum_apply Finset.univ
      (fun i q => ∑ j : I, rr i j q) fun i _ =>
        summable_finset_sum_apply Finset.univ (rr i) fun j _ => hrr i j


theorem lpReplica_disconn_fourFunctions_of_fiberwise
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B C D E F : Finset (LPReplicaCurrentVertex V))
    (hfiber : ∀ m,
      lpReplicaRowFiberMass G sites beta J hf r A B m <=
        lpReplicaRowFiberMass G sites beta J hf r C D m +
          lpReplicaRowFiberMass G sites beta J hf r E F m) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr A ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr B ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <=
      sourcePairDisconnSum H beta Jr C ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr D ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 +
      sourcePairDisconnSum H beta Jr E ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
        sourcePairDisconnSum H beta Jr F ∅
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  dsimp only
  rw [lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
      G sites beta J hf r hbeta hJ hhf hr A B,
    lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
      G sites beta J hf r hbeta hJ hhf hr C D,
    lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
      G sites beta J hf r hbeta hJ hhf hr E F]
  have hAB := lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr A B
  have hCD := lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr C D
  have hEF := lpReplicaRowFiberMass_summable
    G sites beta J hf r hbeta hJ hhf hr E F
  rw [← hCD.tsum_add hEF]
  exact Summable.tsum_le_tsum hfiber hAB (hCD.add hEF)


end
end StatMech.Ising
