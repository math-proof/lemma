/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part5


namespace StatMech

namespace Exact3D

namespace RatInterval

theorem intervalGershgorinRowExcludes_of_endpointSeparated {n : ℕ}
    {I : IntervalMatrix n n} {lam : ℝ} {i : Fin n}
    (hsep : IntervalGershgorinRowEndpointSeparated I lam i) :
    IntervalGershgorinRowExcludes I lam i := by
  intro a ha
  have hR : 0 ≤ (IntervalOffDiagAbsRowSum I i : ℝ) :=
    IntervalOffDiagAbsRowSum_nonneg_real I i
  rcases hsep with hleft | hright
  · have hlt : lam < a := by linarith [ha.1]
    have hdist : |lam - a| = a - lam := by
      rw [abs_sub_comm, abs_of_nonneg]
      linarith
    rw [hdist]
    linarith [ha.1]
  · have hlt : a < lam := by linarith [ha.2]
    have hdist : |lam - a| = lam - a := by
      rw [abs_of_nonneg]
      linarith
    rw [hdist]
    linarith [ha.2]


theorem intervalGershgorinRowEndpointSeparated_of_mem_Icc {n : ℕ}
    {I : IntervalMatrix n n} {lo hi lam : ℝ} {i : Fin n}
    (hsep : IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i)
    (hlam : lam ∈ Set.Icc lo hi) :
    IntervalGershgorinRowEndpointSeparated I lam i := by
  rcases hlam with ⟨hlo, hhi⟩
  rcases hsep with hleft | hright
  · left
    linarith
  · right
    linarith


theorem no_eigenvector_of_gershgorin_exclusion {n : ℕ}
    (A : Fin n → Fin n → ℝ) (lam : ℝ)
    (hexcl : ∀ i, GershgorinRowExcludes A lam i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False := by
  rcases gershgorin_bound_of_eigenvector A x lam heig hnonzero with ⟨i, hi⟩
  exact (not_le_of_gt (hexcl i)) hi


theorem not_exists_eigenvector_of_gershgorin_exclusion {n : ℕ}
    (A : Fin n → Fin n → ℝ) (lam : ℝ)
    (hexcl : ∀ i, GershgorinRowExcludes A lam i) :
    ¬ ∃ x : Fin n → ℝ,
      (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨x, heig, hnonzero⟩
  exact no_eigenvector_of_gershgorin_exclusion A lam hexcl x heig hnonzero


theorem no_eigenvector_of_interval_gershgorin_exclusion {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hexcl : ∀ i, IntervalGershgorinRowExcludes I lam i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False := by
  rcases gershgorin_interval_bound_of_eigenvector hA x lam heig hnonzero with
    ⟨i, hi⟩
  exact (not_le_of_gt (hexcl i (A i i) (hA i i))) hi


theorem not_exists_eigenvector_of_interval_gershgorin_exclusion {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hexcl : ∀ i, IntervalGershgorinRowExcludes I lam i) :
    ¬ ∃ x : Fin n → ℝ,
      (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨x, heig, hnonzero⟩
  exact no_eigenvector_of_interval_gershgorin_exclusion hA lam hexcl x heig
    hnonzero


theorem no_eigenvector_of_interval_gershgorin_endpoint_separation {n : ℕ}
    {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparated I lam i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False :=
  no_eigenvector_of_interval_gershgorin_exclusion hA lam
    (fun i => intervalGershgorinRowExcludes_of_endpointSeparated (hsep i))
    x heig hnonzero


theorem not_exists_eigenvector_of_interval_gershgorin_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lam : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparated I lam i) :
    ¬ ∃ x : Fin n → ℝ,
      (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨x, heig, hnonzero⟩
  exact no_eigenvector_of_interval_gershgorin_endpoint_separation hA lam hsep
    x heig hnonzero


theorem no_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) {lo hi lam : ℝ}
    (hlam : lam ∈ Set.Icc lo hi)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i)
    (x : Fin n → ℝ)
    (heig : ∀ i, matVec A x i = lam * x i)
    (hnonzero : ∃ i, x i ≠ 0) : False :=
  no_eigenvector_of_interval_gershgorin_endpoint_separation hA lam
    (fun i => intervalGershgorinRowEndpointSeparated_of_mem_Icc
      (hsep i) hlam)
    x heig hnonzero


theorem not_exists_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lo hi : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i) :
    ¬ ∃ lam : ℝ, lam ∈ Set.Icc lo hi ∧
      ∃ x : Fin n → ℝ,
        (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 := by
  rintro ⟨lam, hlam, x, heig, hnonzero⟩
  exact
    no_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
      hA hlam hsep x heig hnonzero


theorem not_exists_eigenvector_in_Icc_of_endpoint_separation
    {n : ℕ} {A : Fin n → Fin n → ℝ} {I : IntervalMatrix n n}
    (hA : MatrixMem A I) (lo hi : ℝ)
    (hsep : ∀ i, IntervalGershgorinRowEndpointSeparatedOnIcc I lo hi i) :
    ¬ ∃ lam : ℝ, lam ∈ Set.Icc lo hi ∧
      ∃ x : Fin n → ℝ,
        (∀ i, matVec A x i = lam * x i) ∧ ∃ i, x i ≠ 0 :=
  not_exists_eigenvector_with_eigenvalue_in_Icc_of_interval_gershgorin_endpoint_separation
    hA lo hi hsep


end RatInterval
end Exact3D
end StatMech
