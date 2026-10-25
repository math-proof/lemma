/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part39
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff
    {n : ℕ} {v : FK.boxVerts 3 n} {k : ℕ}
    {R : Finset (Option (FK.boxVerts 3 n))} :
    R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k ↔
      R ⊆ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v ∧
        R.card = k := by
  simp [finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet]

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_subset_unmarkedOptions
    {n : ℕ} {v : FK.boxVerts 3 n} {k : ℕ}
    {R : Finset (Option (FK.boxVerts 3 n))}
    (hR :
      R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k) :
    R ⊆ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
  (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff.mp
    hR).1

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq
    {n : ℕ} {v : FK.boxVerts 3 n} {k : ℕ}
    {R : Finset (Option (FK.boxVerts 3 n))}
    (hR :
      R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k) :
    R.card = k :=
  (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff.mp
    hR).2

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_nonempty_iff
    {n : ℕ} {v : FK.boxVerts 3 n} {k : ℕ} :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k).Nonempty ↔
      k ≤ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
  simpa [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet,
    Finset.powersetCard_eq_filter]
    using
      (Finset.powersetCard_nonempty
        (s := finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v)
        (n := k))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_powersetCard
    {n : ℕ} (v : FK.boxVerts 3 n) (k : ℕ) :
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k =
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powersetCard
        k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet,
    Finset.powersetCard_eq_filter]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose
    {n : ℕ} (v : FK.boxVerts 3 n) (k : ℕ) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k).card =
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card).choose
        k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_powersetCard,
    Finset.card_powersetCard]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_zero_eq_singleton_empty
    {n : ℕ} (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 0 =
      ({∅} : Finset (Finset (Option (FK.boxVerts 3 n)))) := by
  classical
  ext R
  constructor
  · intro hR
    have hcard : R.card = 0 :=
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq
        hR
    have hRempty : R = ∅ := Finset.card_eq_zero.mp hcard
    simp [hRempty]
  · intro hR
    have hRempty : R = ∅ := by
      simpa using hR
    rw [finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff]
    constructor
    · intro x hx
      simp [hRempty] at hx
    · simp [hRempty]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_zero_sum_eq_empty
    {n : ℕ} (v : FK.boxVerts 3 n)
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v 0,
        f R) = f ∅ := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_zero_eq_singleton_empty]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
    {n : ℕ} (v : FK.boxVerts 3 n)
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v 1,
        f R) =
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        f ({x} : Finset (Option (FK.boxVerts 3 n))) := by
  classical
  let U := finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v
  have hdomain :
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v 1 =
        U.image
          (fun x => ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
    ext R
    constructor
    · intro hR
      have hsub :
          R ⊆ U :=
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_subset_unmarkedOptions
          hR
      have hcard : R.card = 1 :=
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq
          hR
      rcases Finset.card_eq_one.mp hcard with ⟨x, hxR⟩
      have hxU : x ∈ U := by
        exact hsub (by rw [hxR]; simp)
      exact Finset.mem_image.mpr ⟨x, hxU, hxR.symm⟩
    · intro hR
      rcases Finset.mem_image.mp hR with ⟨x, hxU, hxR⟩
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff]
      constructor
      · intro y hy
        have hyx : y = x := by
          have hySingleton :
              y ∈ ({x} : Finset (Option (FK.boxVerts 3 n))) := by
            simpa [hxR] using hy
          simpa using hySingleton
        simpa [hyx] using hxU
      · rw [← hxR]
        simp
  rw [hdomain]
  rw [Finset.sum_image]
  intro x _hxU y _hyU hxy
  have hxMemY : x ∈ ({y} : Finset (Option (FK.boxVerts 3 n))) := by
    have hxMemX : x ∈ ({x} : Finset (Option (FK.boxVerts 3 n))) := by
      simp
    simpa [hxy] using hxMemX
  simpa using hxMemY

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose_boxVerts_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) (k : ℕ) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k).card =
      Nat.choose (Fintype.card (FK.boxVerts 3 n) - 2) k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose,
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
      hv]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) (k : ℕ) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k).card =
      Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose_boxVerts_sub_two_of_boundary
      hv k,
    StatMech.FK.ecz_boxVerts_card]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_nonempty_iff_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) {k : ℕ} :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k).Nonempty ↔
      k ≤ (2 * n + 1) ^ 3 - 2 := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_nonempty_iff,
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
      hv,
    StatMech.FK.ecz_boxVerts_card]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_empty_iff
    {n : ℕ} {v : FK.boxVerts 3 n} {k : ℕ} :
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k =
        ∅ ↔
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card < k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_powersetCard,
    Finset.powersetCard_eq_empty]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_empty_iff_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) {k : ℕ} :
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k = ∅ ↔
      (2 * n + 1) ^ 3 - 2 < k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_empty_iff,
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
      hv,
    StatMech.FK.ecz_boxVerts_card]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_sum_eq_zero_of_card_lt
    {n : ℕ} {v : FK.boxVerts 3 n} {k : ℕ}
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M)
    (hk : (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card < k) :
    (∑ R ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k,
        f R) = 0 := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_empty_iff.mpr
      hk]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_sum_eq_zero_of_box_volume_sub_two_lt
    {n : ℕ} {v : FK.boxVerts 3 n} {k : ℕ}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M)
    (hk : (2 * n + 1) ^ 3 - 2 < k) :
    (∑ R ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k,
        f R) = 0 :=
  finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_sum_eq_zero_of_card_lt
    f
    (by
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
          hv,
        StatMech.FK.ecz_boxVerts_card]
      exact hk)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_pairwiseDisjoint
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
      v hasGhost hasOrigin hasEndpoint : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k =>
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k) := by
  intro k _hk l _hl hkl
  change Disjoint
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k)
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v l)
  rw [Finset.disjoint_left]
  intro R hRk hRl
  have hkeq : k = l := by
    calc
      k = R.card :=
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq
          hRk).symm
      _ = l :=
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq
          hRl
  exact hkl hkeq

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_eq_biUnion_exactCardSet
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)) =
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint).biUnion
        (fun k =>
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k) := by
  ext R
  constructor
  · intro hR
    have hpow :
        R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset :=
      (Finset.mem_filter.mp hR).1
    have hthreshold :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card :=
      (Finset.mem_filter.mp hR).2
    have hcardLe :
        R.card ≤
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
      Finset.card_le_card (Finset.mem_powerset.mp hpow)
    refine Finset.mem_biUnion.mpr ⟨R.card, ?_, ?_⟩
    · exact
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mpr
          ⟨hthreshold, hcardLe⟩
    · exact
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff.mpr
          ⟨Finset.mem_powerset.mp hpow, rfl⟩
  · intro hR
    rcases Finset.mem_biUnion.mp hR with ⟨k, hk, hRk⟩
    have hsubset :
        R ⊆ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_subset_unmarkedOptions
        hRk
    have hcard :
        R.card = k :=
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq
        hRk
    have hthreshold :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ k :=
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_threshold_le
        hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hsubset, by simpa [hcard] using hthreshold⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_exactCardSet
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool)
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤ R.card)),
        f R) =
      ∑ k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint,
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_eq_biUnion_exactCardSet]
  exact Finset.sum_biUnion
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_pairwiseDisjoint
      v hasGhost hasOrigin hasEndpoint)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤ R.card)),
        f R) =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_exactCardSet,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv hasGhost hasOrigin hasEndpoint]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_false_false_false_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            false false false ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv false false false f

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_false_false_true_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            false false true ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv false false true f

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_false_true_false_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            false true false ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv false true false f

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_false_true_true_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            false true true ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv false true true f

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_true_false_false_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            true false false ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv true false false f

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_true_false_true_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            true false true ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv true false true f

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_true_true_false_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            true true false ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv true true false f

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_true_true_true_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Option (FK.boxVerts 3 n)) → M) :
    (∑ R ∈
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            true true true ≤ R.card)),
        f R) =
      ∑ k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2),
        ∑ R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k,
          f R := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_sum_eq_sum_Icc_exactCardSet_box_volume_sub_two_of_boundary
      hv true true true f

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_exactCardSet_card
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card =
      ∑ k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint,
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k).card := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_eq_biUnion_exactCardSet]
  exact Finset.card_biUnion
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_pairwiseDisjoint
      v hasGhost hasOrigin hasEndpoint)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_choose
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card =
      ∑ k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint,
        Nat.choose
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card
          k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_exactCardSet_card]
  exact Finset.sum_congr rfl
    (fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose
        v k)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card =
      ∑ k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint,
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_exactCardSet_card]
  exact Finset.sum_congr rfl
    (fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose_box_volume_sub_two_of_boundary
        hv k)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_choose_box_volume_sub_two_of_boundary
      hv hasGhost hasOrigin hasEndpoint,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv hasGhost hasOrigin hasEndpoint]

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_false_false_false_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false false false ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv false false false

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_false_false_true_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false false true ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv false false true

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_false_true_false_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false true false ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv false true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_false_true_true_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          false true true ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv false true true

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_true_false_false_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true false false ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv true false false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_true_false_true_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true false true ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv true false true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_true_true_false_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true true false ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv true true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_true_true_true_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          true true true ≤ R.card)).card =
      ∑ k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2),
        Nat.choose ((2 * n + 1) ^ 3 - 2) k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_eq_sum_Icc_choose_box_volume_sub_two_of_boundary
      hv true true true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_subset_powerset
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)) ⊆
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset := by
  intro R hR
  exact (Finset.mem_filter.mp hR).1

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_le_two_pow
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card ≤
      2 ^ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
  calc
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card
        ≤ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.card :=
      Finset.card_le_card
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_subset_powerset
          v hasGhost hasOrigin hasEndpoint)
    _ = 2 ^ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
      rw [Finset.card_powerset]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_le_two_pow_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card ≤
      2 ^ ((2 * n + 1) ^ 3 - 2) := by
  calc
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card)).card
        ≤ 2 ^ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualThresholdSet_card_le_two_pow
        v hasGhost hasOrigin hasEndpoint
    _ = 2 ^ ((2 * n + 1) ^ 3 - 2) := by
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
          hv,
        StatMech.FK.ecz_boxVerts_card]

end Exact3D
end StatMech
