/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Def.Analysis.CStarAlgebra.KadisonSinger.Paving.Part6
open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

lemma ksBlock_outcome_eq {m d r : ℕ} (u : Fin m → Fin d → ℂ)
    (c : Fin m → Fin r) (j : Fin r) :
    ksBlock (∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
      (star (ksLiftVector (c i) (u i)))) j = (r : ℂ) • ksColorGram u c j := by
  apply funext
  intro a
  apply funext
  intro b
  change ksMatrixEntryLM (j, a) (j, b)
      (∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
        (star (ksLiftVector (c i) (u i)))) =
    ksMatrixEntryLM a b ((r : ℂ) • ksColorGram u c j)
  simp only [ksColorGram, map_sum, map_smul, ksMatrixEntryLM, smul_eq_mul]
  change (∑ i, ksLiftVector (c i) (u i) (j, a) *
      star (ksLiftVector (c i) (u i) (j, b))) =
    (r : ℂ) * ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
      u i a * star (u i b)
  rw [Finset.mul_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : c i = j
  · subst j
    simp only [ksLiftVector, ite_true, map_mul, RCLike.star_def, Complex.conj_ofReal]
    calc
      ↑√↑r * u i a * (↑√↑r * (starRingEnd ℂ) (u i b)) =
          ((↑√↑r * ↑√↑r) * (u i a * (starRingEnd ℂ) (u i b))) := by ring
      _ = (r : ℂ) * (u i a * (starRingEnd ℂ) (u i b)) := by
        norm_cast
        rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
        norm_num
  · have hjc : j ≠ c i := Ne.symm hc
    simp [ksLiftVector, hc, hjc]

lemma ksMSS_rescale {r : ℕ} (hr : 0 < r) {δ : ℝ} :
    (1 + Real.sqrt (r * δ)) ^ 2 / r =
      (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := by
  rw [Real.sqrt_mul (Nat.cast_nonneg r)]
  have hspos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hr)
  have hsne : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt hspos
  have hs2 : Real.sqrt (r : ℝ) ^ 2 = r := Real.sq_sqrt (Nat.cast_nonneg r)
  field_simp [hsne]
  nlinarith

theorem ksExists_fin_frame_partition
    (hMSS : FiniteMSSBound.{0}) {m d r : ℕ} (hr : 0 < r)
    (u : Fin m → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1)
    (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) :
    ∃ c : Fin m → Fin r, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin d) (Fin d) ℂ)‖ ≤
          (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := by
  cases d with
  | zero =>
      let c : Fin m → Fin r := fun _ ↦ ⟨0, hr⟩
      refine ⟨c, ?_⟩
      intro j
      have hzero :
          ((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
            Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin 0) (Fin 0) ℂ) = 0 :=
        Subsingleton.elim _ _
      rw [hzero, norm_zero]
      positivity
  | succ d =>
      obtain ⟨c, hc⟩ := ksMSS_outcome_for_frame hMSS hr u δ hδ hframe hu
      refine ⟨c, ?_⟩
      intro j
      let M : Matrix (Fin r × Fin (d + 1)) (Fin r × Fin (d + 1)) ℂ :=
        ∑ i, Matrix.vecMulVec (ksLiftVector (c i) (u i))
          (star (ksLiftVector (c i) (u i)))
      have hfull : ksOperatorNorm M ≤ (1 + Real.sqrt (r * δ)) ^ 2 := by
        unfold ksOperatorNorm ksMatrixCLM
        rw [← Matrix.l2_opNorm_def]
        exact hc
      have hblock : ksOperatorNorm (ksBlock M j) ≤
          (1 + Real.sqrt (r * δ)) ^ 2 :=
        (ksBlock_norm_le M j).trans hfull
      have hblock_eq : ksBlock M j = (r : ℂ) • ksColorGram u c j := by
        exact ksBlock_outcome_eq u c j
      rw [hblock_eq] at hblock
      have hscale : ksOperatorNorm ((r : ℂ) • ksColorGram u c j) =
          r * ‖ksColorGram u c j‖ := by
        unfold ksOperatorNorm ksMatrixCLM
        rw [← Matrix.l2_opNorm_def, norm_smul]
        simp
      rw [hscale] at hblock
      change ‖ksColorGram u c j‖ ≤ (1 / Real.sqrt r + Real.sqrt δ) ^ 2
      calc
        ‖ksColorGram u c j‖ ≤ (1 + Real.sqrt (r * δ)) ^ 2 / r :=
          (le_div_iff₀ (Nat.cast_pos.2 hr)).2 (by simpa [mul_comm] using hblock)
        _ = (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := ksMSS_rescale hr

/-- The finite MSS random-vector bound partitions a finite Parseval frame into uniformly bounded
subframes. -/
theorem exists_frame_partition_of_finiteMSS
    (hMSS : FiniteMSSBound.{0}) {I : Type v} [Fintype I] {d r : ℕ}
    (hr : 0 < r) (u : I → Fin d → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1)
    (hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ δ) :
    ∃ c : I → Fin r, ∀ j,
      ‖((∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin d) (Fin d) ℂ)‖ ≤
          (1 / Real.sqrt r + Real.sqrt δ) ^ 2 := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let v : Fin (Fintype.card I) → Fin d → ℂ := fun i ↦ u (e.symm i)
  have hv_frame : ∑ i, Matrix.vecMulVec (v i) (star (v i)) = 1 := by
    exact (e.symm.sum_comp (fun i ↦ Matrix.vecMulVec (u i) (star (u i)))).trans hframe
  have hv_norm : ∀ i, ∑ k, ‖v i k‖ ^ 2 ≤ δ := by
    intro i
    exact hu (e.symm i)
  obtain ⟨c, hc⟩ := ksExists_fin_frame_partition hMSS hr v δ hδ hv_frame hv_norm
  let c' : I → Fin r := fun i ↦ c (e i)
  refine ⟨c', ?_⟩
  intro j
  have hsum :
      ((∑ i ∈ Finset.univ.filter (fun i ↦ c' i = j),
        Matrix.vecMulVec (u i) (star (u i))) : Matrix (Fin d) (Fin d) ℂ) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j),
        Matrix.vecMulVec (v i) (star (v i)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    simpa [c', v] using e.sum_comp (fun i ↦
      if c i = j then Matrix.vecMulVec (v i) (star (v i)) else 0)
  rw [hsum]
  exact hc j

theorem ksPositive_half_paving
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hdiag : ∀ i, B i i = (((1 / 2 : ℝ) : ℂ))) :
    ∃ c : Fin n → Fin r, ∀ j,
      ‖ksPavingProj c j * B * ksPavingProj c j‖ ≤
        (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 := by
  let S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt B
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt (1 - B)
  let u : Fin n ⊕ Fin n → Fin n → ℂ :=
    Sum.elim (fun i k ↦ S k i) (fun i k ↦ T k i)
  have hSstar : Matrix.conjTranspose S = S :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).isHermitian.eq
  have hTstar : Matrix.conjTranspose T = T :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (1 - B))).isHermitian.eq
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB0
  have hTT : T * T = 1 - B :=
    CFC.sqrt_mul_sqrt_self (1 - B) (sub_nonneg.mpr hB1)
  have hframe : ∑ i, Matrix.vecMulVec (u i) (star (u i)) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ i, Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))) +
      ∑ i, Matrix.vecMulVec (fun k ↦ T k i) (star (fun k ↦ T k i)) = 1
    rw [ksAll_columns, ksAll_columns, hSstar, hTstar, hSS, hTT]
    noncomm_ring
  have hu : ∀ i, ∑ k, ‖u i k‖ ^ 2 ≤ (1 / 2 : ℝ) := by
    intro i
    cases i with
    | inl i =>
        change ∑ k, ‖S k i‖ ^ 2 ≤ (1 / 2 : ℝ)
        have hcol := ksColumn_norm_sq S B (by simpa [hSstar] using hSS) i
        have heq : (∑ k, ‖S k i‖ ^ 2 : ℝ) = 1 / 2 := by
          apply Complex.ofReal_injective
          exact hcol.trans (hdiag i)
        exact heq.le
    | inr i =>
        change ∑ k, ‖T k i‖ ^ 2 ≤ (1 / 2 : ℝ)
        have hcol := ksColumn_norm_sq T (1 - B) (by simpa [hTstar] using hTT) i
        have hcomp : (1 - B) i i = (((1 / 2 : ℝ) : ℂ)) := by
          simp [hdiag i]
          norm_num
        have heq : (∑ k, ‖T k i‖ ^ 2 : ℝ) = 1 / 2 := by
          apply Complex.ofReal_injective
          exact hcol.trans hcomp
        exact heq.le
  obtain ⟨cSum, hcSum⟩ :=
    exists_frame_partition_of_finiteMSS hMSS hr u (1 / 2) (by norm_num) hframe hu
  let c : Fin n → Fin r := fun i ↦ cSum (Sum.inl i)
  refine ⟨c, ?_⟩
  intro j
  let L : Matrix (Fin n) (Fin n) ℂ :=
    ∑ i ∈ Finset.univ.filter (fun i ↦ cSum (Sum.inl i) = j),
      Matrix.vecMulVec (fun k ↦ S k i) (star (fun k ↦ S k i))
  let R : Matrix (Fin n) (Fin n) ℂ :=
    ∑ i ∈ Finset.univ.filter (fun i ↦ cSum (Sum.inr i) = j),
      Matrix.vecMulVec (fun k ↦ T k i) (star (fun k ↦ T k i))
  let G : Matrix (Fin n) (Fin n) ℂ :=
    ∑ i ∈ Finset.univ.filter (fun i ↦ cSum i = j),
      Matrix.vecMulVec (u i) (star (u i))
  have hG : G = L + R := by
    simp only [G, L, R, Finset.sum_filter]
    rw [Fintype.sum_sum_type]
    rfl
  have hL0 : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro i hi
    exact (Matrix.posSemidef_vecMulVec_self_star _).nonneg
  have hR0 : 0 ≤ R := by
    apply Finset.sum_nonneg
    intro i hi
    exact (Matrix.posSemidef_vecMulVec_self_star _).nonneg
  have hLG : L ≤ G := by
    rw [hG]
    exact le_add_of_nonneg_right hR0
  have hLnorm : ‖L‖ ≤ (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 :=
    (CStarAlgebra.norm_le_norm_of_le_of_nonneg hLG hL0).trans (hcSum j)
  have hL : L = S * ksPavingProj c j * Matrix.conjTranspose S := by
    exact ksFiltered_columns S c j
  let Q := ksPavingProj c j
  let X := S * Q
  have hQstar : Matrix.conjTranspose Q = Q := ksPavingProj_star c j
  have hQsq : Q * Q = Q := ksPavingProj_sq c j
  have hleft : S * Q * Matrix.conjTranspose S = X * star X := by
    rw [hSstar]
    simp only [X, star_mul, Matrix.star_eq_conjTranspose, hQstar, hSstar]
    calc
      S * Q * S = S * (Q * S) := Matrix.mul_assoc S Q S
      _ = S * ((Q * Q) * S) := by rw [hQsq]
      _ = (S * Q) * (Q * S) := by simp only [Matrix.mul_assoc]
  have hright : Q * B * Q = star X * X := by
    simp only [X, star_mul, Matrix.star_eq_conjTranspose, hQstar, hSstar]
    rw [← hSS]
    simp [Matrix.mul_assoc]
  change ‖Q * B * Q‖ ≤ _
  calc
    ‖Q * B * Q‖ = ‖star X * X‖ := congrArg norm hright
    _ = ‖X‖ * ‖X‖ := CStarRing.norm_star_mul_self
    _ = ‖X * star X‖ := CStarRing.norm_self_mul_star.symm
    _ = ‖S * Q * Matrix.conjTranspose S‖ := congrArg norm hleft.symm
    _ = ‖L‖ := congrArg norm hL.symm
    _ ≤ _ := hLnorm

theorem ksPositive_half_paving_order
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hdiag : ∀ i, B i i = (((1 / 2 : ℝ) : ℂ))) :
    ∃ c : Fin n → Fin r, ∀ j,
      ksPavingProj c j * B * ksPavingProj c j ≤
        (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 • ksPavingProj c j := by
  obtain ⟨c, hc⟩ := ksPositive_half_paving hMSS hr B hB0 hB1 hdiag
  refine ⟨c, ?_⟩
  intro j
  exact ksCompression_le_smul_projection B hB0 c j _ (hc j)

theorem ksHermitian_paving_of_mss
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hdiagA : ∀ i, A i i = 0) (hnormA : ‖A‖ ≤ 1) :
    ∃ c : Fin n → Fin (r * r), ∀ j,
      ‖ksPavingProj c j * A * ksPavingProj c j‖ ≤
        2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 := by
  have hAself : IsSelfAdjoint A := hA.isSelfAdjoint
  have hmap : (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖A‖ ≤
      (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := by
    simp only [Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right hnormA
      (show 0 ≤ (1 : Matrix (Fin n) (Fin n) ℂ) from zero_le_one)
  have hAle : A ≤ 1 := by
    calc
      A ≤ (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖A‖ :=
        IsSelfAdjoint.le_algebraMap_norm_self A hAself
      _ ≤ (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := hmap
      _ = 1 := by simp
  have hnegOneLe : -(1 : Matrix (Fin n) (Fin n) ℂ) ≤ A := by
    calc
      -(1 : Matrix (Fin n) (Fin n) ℂ) =
          -(algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := by simp
      _ ≤ -(algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ)) ‖A‖ := neg_le_neg hmap
      _ ≤ A := IsSelfAdjoint.neg_algebraMap_norm_le_self A hAself
  let Bp : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (1 + A)
  let Bm : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (1 - A)
  have hBp0 : 0 ≤ Bp := by
    have hsum : 0 ≤ (1 : Matrix (Fin n) (Fin n) ℂ) + A := by
      have hs := add_le_add_left hnegOneLe 1
      simpa [add_comm] using hs
    exact smul_nonneg (by norm_num) hsum
  have hBp1 : Bp ≤ 1 := by
    have hs : (1 : Matrix (Fin n) (Fin n) ℂ) + A ≤ 1 + 1 :=
      by simpa [add_comm] using add_le_add_left hAle 1
    change (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + A) ≤ 1
    calc
      (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + A) ≤
          (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) :=
        smul_le_smul_of_nonneg_left hs (by norm_num)
      _ = 1 := by module
  have hBm0 : 0 ≤ Bm := by
    exact smul_nonneg (by norm_num) (sub_nonneg.mpr hAle)
  have hBm1 : Bm ≤ 1 := by
    have hnegA : -A ≤ (1 : Matrix (Fin n) (Fin n) ℂ) := by
      simpa using neg_le_neg hnegOneLe
    have hs : (1 : Matrix (Fin n) (Fin n) ℂ) - A ≤ 1 + 1 := by
      simpa [sub_eq_add_neg] using add_le_add_left hnegA 1
    change (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) - A) ≤ 1
    calc
      (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) - A) ≤
          (1 / 2 : ℝ) • ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) :=
        smul_le_smul_of_nonneg_left hs (by norm_num)
      _ = 1 := by module
  have hBpdiag : ∀ i, Bp i i = (((1 / 2 : ℝ) : ℂ)) := by
    intro i
    simp [Bp, hdiagA i]
  have hBmdiag : ∀ i, Bm i i = (((1 / 2 : ℝ) : ℂ)) := by
    intro i
    simp [Bm, hdiagA i]
  obtain ⟨cp, hcp⟩ := ksPositive_half_paving_order hMSS hr Bp hBp0 hBp1 hBpdiag
  obtain ⟨cm, hcm⟩ := ksPositive_half_paving_order hMSS hr Bm hBm0 hBm1 hBmdiag
  let c : Fin n → Fin (r * r) := fun i ↦ finProdFinEquiv (cp i, cm i)
  refine ⟨c, ?_⟩
  intro j
  let p : Fin r × Fin r := finProdFinEquiv.symm j
  have hp : ∀ i, c i = j → cp i = p.1 := by
    intro i hi
    have hpairs : (cp i, cm i) = p := by
      simpa [c, p] using congrArg finProdFinEquiv.symm hi
    exact congrArg Prod.fst hpairs
  have hm : ∀ i, c i = j → cm i = p.2 := by
    intro i hi
    have hpairs : (cp i, cm i) = p := by
      simpa [c, p] using congrArg finProdFinEquiv.symm hi
    exact congrArg Prod.snd hpairs
  let α : ℝ := (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2
  let β : ℝ := 2 * α - 1
  have hpBound : ksPavingProj c j * Bp * ksPavingProj c j ≤ α • ksPavingProj c j :=
    ksRefine_order_bound Bp α c j cp p.1 hp (hcp p.1)
  have hmBound : ksPavingProj c j * Bm * ksPavingProj c j ≤ α • ksPavingProj c j :=
    ksRefine_order_bound Bm α c j cm p.2 hm (hcm p.2)
  let Q := ksPavingProj c j
  let X := Q * A * Q
  have hQsq : Q * Q = Q := ksPavingProj_sq c j
  have hplusId : (2 : ℝ) • Bp = 1 + A := by
    simp [Bp, smul_smul]
  have hminusId : (2 : ℝ) • Bm = 1 - A := by
    simp [Bm, smul_smul]
  have hXplus : X = (2 : ℝ) • (Q * Bp * Q) - Q := by
    symm
    calc
      (2 : ℝ) • (Q * Bp * Q) - Q = Q * ((2 : ℝ) • Bp) * Q - Q := by
        simp only [mul_smul_comm, smul_mul_assoc]
      _ = Q * (1 + A) * Q - Q := by rw [hplusId]
      _ = X := by simp [X, mul_add, add_mul, hQsq]
  have hXminus : -X = (2 : ℝ) • (Q * Bm * Q) - Q := by
    calc
      -X = Q * (1 - A) * Q - Q := by simp [X, mul_sub, sub_mul, hQsq]
      _ = Q * ((2 : ℝ) • Bm) * Q - Q := by rw [hminusId]
      _ = (2 : ℝ) • (Q * Bm * Q) - Q := by
        simp only [mul_smul_comm, smul_mul_assoc]
  have hupper : X ≤ β • Q := by
    rw [hXplus]
    calc
      (2 : ℝ) • (Q * Bp * Q) - Q ≤ (2 : ℝ) • (α • Q) - Q :=
        sub_le_sub_right (smul_le_smul_of_nonneg_left hpBound (by norm_num)) Q
      _ = β • Q := by
        simp [β, smul_smul]
        module
  have hnegUpper : -X ≤ β • Q := by
    rw [hXminus]
    calc
      (2 : ℝ) • (Q * Bm * Q) - Q ≤ (2 : ℝ) • (α • Q) - Q :=
        sub_le_sub_right (smul_le_smul_of_nonneg_left hmBound (by norm_num)) Q
      _ = β • Q := by
        simp [β, smul_smul]
        module
  have hbeta : 0 ≤ β := by
    have hx : 0 ≤ 1 / Real.sqrt (r : ℝ) := by positivity
    have hy : 0 ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
    have hy2 : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    dsimp [β, α]
    nlinarith [mul_nonneg hx hy]
  have hQnorm : ‖Q‖ ≤ 1 := ksPavingProj_norm_le c j
  have hendpoint : ‖β • Q‖ ≤ β := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta]
    nlinarith [norm_nonneg Q]
  have hXself : IsSelfAdjoint X := by
    have hXherm := Matrix.isHermitian_conjTranspose_mul_mul Q hA
    rw [ksPavingProj_star c j] at hXherm
    exact hXherm.isSelfAdjoint
  change ‖X‖ ≤ β
  calc
    ‖X‖ ≤ max ‖-(β • Q)‖ ‖β • Q‖ :=
      IsSelfAdjoint.norm_le_max_of_le_of_le (neg_le.mpr hnegUpper) hupper hXself
    _ = ‖β • Q‖ := by simp
    _ ≤ β := hendpoint

/-- A quantitative Anderson paving bound follows from the finite MSS random-vector bound. -/
theorem andersonPaving_of_finiteMSS
    (hMSS : FiniteMSSBound.{0}) {n r : ℕ} (hr : 0 < r)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hdiagA : ∀ i, A i i = 0) (hnormA : ‖A‖ ≤ 1) :
    ∃ c : Fin n → Fin (r * r), ∀ j,
      ‖Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0) * A *
        Matrix.diagonal (fun i ↦ if c i = j then (1 : ℂ) else 0)‖ ≤
          2 * (1 / Real.sqrt r + Real.sqrt (1 / 2 : ℝ)) ^ 2 - 1 := by
  simpa only [ksPavingProj] using
    ksHermitian_paving_of_mss hMSS hr A hA hdiagA hnormA

end Analysis.CStarAlgebra.KadisonSinger
