/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part9
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleStraightExtendBalancedFibers_injective
    {N M r : ℕ} (hN : Even (N + 1)) (hr : Even r) (q : ℕ) :
    Function.Injective
      (sixVertexRectangleStraightExtendBalancedFibers
        (M := M) hN hr q) := by
  rintro ⟨⟨ξ, hξ⟩, ω⟩ ⟨⟨η, hη⟩, ν⟩ h
  have hext := congrArg
    (fun x : SixVertexRectangleBalancedBoundaryFibers
        ((N + 1) + r) ((M + 1) + q) => x.2.1) h
  have hων : ω.1 = ν.1 :=
    sixVertexRectangleStraightExtend_injective
      (sixVertexHalfFilledRow r) hext
  have hrect : sixVertexToroidalRectangleBoundary ξ =
      sixVertexToroidalRectangleBoundary η := by
    rw [← ω.2, ← ν.2, hων]
  have hξη : ξ = η := by
    apply Prod.ext
    · funext j
      have hleft := congrArg (fun b => b.left j) hrect
      simpa [sixVertexToroidalRectangleBoundary] using hleft
    · funext i
      have hbottom := congrArg (fun b => b.bottom i) hrect
      simpa [sixVertexToroidalRectangleBoundary] using hbottom
  subst η
  have hsub : (⟨ξ, hξ⟩ : {ξ : SixVertexToroidalBoundary (N + 1) (M + 1) //
      ξ.Balanced}) = ⟨ξ, hη⟩ := Subtype.ext rfl
  apply Sigma.ext hsub
  cases hsub
  exact heq_of_eq (Subtype.ext hων)

theorem sixVertexRectangleStraightExtendBalancedFibers_weight
    {N M r : ℕ} (hN : Even (N + 1)) (hr : Even r) (q : ℕ)
    (c : ℝ) (ξω : SixVertexRectangleBalancedBoundaryFibers
      (N + 1) (M + 1)) :
    ((sixVertexRectangleStraightExtendBalancedFibers hN hr q ξω).2.1).weight c =
      ξω.2.1.weight c := by
  exact sixVertexRectangleStraightExtend_weight c
    (sixVertexHalfFilledRow r) ξω.2.1


theorem sixVertexRectangleBalancedPartitionSum_le_straightExtend
    {N M r : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : Even (N + 1)) (hr : Even r) (q : ℕ) :
    sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ≤
      sixVertexRectangleBalancedPartitionSum
        ((N + 1) + r) ((M + 1) + q) c := by
  rw [sixVertexRectangleBalancedPartitionSum_eq_fiberSum,
    sixVertexRectangleBalancedPartitionSum_eq_fiberSum]
  let extend := sixVertexRectangleStraightExtendBalancedFibers
    (M := M) hN hr q
  calc
    (∑ ξω : SixVertexRectangleBalancedBoundaryFibers (N + 1) (M + 1),
      ξω.2.1.weight c) =
        ∑ ξω : SixVertexRectangleBalancedBoundaryFibers (N + 1) (M + 1),
          (extend ξω).2.1.weight c := by
      apply Fintype.sum_congr
      intro ξω
      exact (sixVertexRectangleStraightExtendBalancedFibers_weight
        hN hr q c ξω).symm
    _ = ∑ η ∈ Finset.univ.image extend, η.2.1.weight c := by
      rw [Finset.sum_image
        (sixVertexRectangleStraightExtendBalancedFibers_injective
          (M := M) hN hr q).injOn]
    _ ≤ ∑ η : SixVertexRectangleBalancedBoundaryFibers
          ((N + 1) + r) ((M + 1) + q), η.2.1.weight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro η hη hnot
        exact SixVertexRectangleArrows.weight_nonneg hc η.2.1


theorem sixVertexRectangleBalancedPartitionSum_pow_mulFactors_le
    {N M A B : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hA : 0 < A) (hB : 0 < B) :
    sixVertexRectangleBalancedPartitionSum N M c ^ (A * B) ≤
      ((2 : ℝ) ^ (N + M)) ^ (A * B) *
        sixVertexRectangleBalancedPartitionSum (A * N) (B * M) c := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hA.ne'
  obtain ⟨B, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hB.ne'
  exact sixVertexRectangleBalancedPartitionSum_pow_blockCount_le hc hNeven


theorem sixVertexRectangleBalancedPartitionSum_le_straightExtend_general
    {N M r q : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N) (hr : Even r) :
    sixVertexRectangleBalancedPartitionSum N M c ≤
      sixVertexRectangleBalancedPartitionSum (N + r) (M + q) c := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  exact sixVertexRectangleBalancedPartitionSum_le_straightExtend
    hc hNeven hr q


theorem sixVertexRectangleBalancedPartitionSum_blockRepetition
    {N M n m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hn : N < n) (hm : M < m) (hneven : Even n) :
    sixVertexRectangleBalancedPartitionSum N M c ^
        ((n / N) * (m / M)) ≤
      ((2 : ℝ) ^ (N + M)) ^ ((n / N) * (m / M)) *
        sixVertexRectangleBalancedPartitionSum n m c := by
  let A := n / N
  let B := m / M
  let r := n % N
  let q := m % M
  have hA : 0 < A := Nat.div_pos hn.le hN
  have hB : 0 < B := Nat.div_pos hm.le hM
  have hAN : 0 < A * N := Nat.mul_pos hA hN
  have hBM : 0 < B * M := Nat.mul_pos hB hM
  have hANeven : Even (A * N) := hNeven.mul_left A
  have hr : Even r := by
    exact (Even.mod_even_iff hNeven).mpr hneven
  have hn_decomp : A * N + r = n := by
    dsimp [A, r]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n N
  have hm_decomp : B * M + q = m := by
    dsimp [B, q]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod m M
  have hexact := sixVertexRectangleBalancedPartitionSum_pow_mulFactors_le
    hc hN hM hNeven hA hB
  have hextend :=
    sixVertexRectangleBalancedPartitionSum_le_straightExtend_general
      (N := A * N) (M := B * M) (r := r) (q := q)
      hc hAN hBM hANeven hr
  calc
    sixVertexRectangleBalancedPartitionSum N M c ^ (A * B) ≤
        ((2 : ℝ) ^ (N + M)) ^ (A * B) *
          sixVertexRectangleBalancedPartitionSum (A * N) (B * M) c := hexact
    _ ≤ ((2 : ℝ) ^ (N + M)) ^ (A * B) *
          sixVertexRectangleBalancedPartitionSum n m c := by
      rw [← hn_decomp, ← hm_decomp]
      gcongr


end StatMech.FrontierD
