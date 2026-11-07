import Lemma.Matrix.All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef
import Lemma.Matrix.Any_And_Eq_Mul_Adjoint.of.PosDef
import Lemma.Matrix.IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0
import Mathlib.Analysis.RCLike.Sqrt
import Notation.Analysis.Complex.Star
open Matrix
open scoped ComplexOrder


@[path]
private lemma main
  {n : ℕ}
  {A L : Matrix (Fin n) (Fin n) ℂ}
  {t : ℕ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ~x ⬝ᵥ A *ᵥ x)
  (h₂ : ∀ i j : Fin n, L[i][j] = if j < i then (A[i][j] - ∑ k ∈ Finset.Iio j, L[i][k] * ~L[j][k]) / L[j][j] else if j = i then (A[i][i] - ∑ k ∈ Finset.Iio i, ‖L[i][k]‖ ^ 2).sqrt else 0) :
-- imply
  ∀ i : Fin n, i.val < t → 0 < L[i][i] ∧ A[i][i] = ((∑ k ∈ Finset.Iic i, ‖L[i][k]‖ ^ 2 : ℝ) : ℂ) ∧ ∀ j : Fin n, j < i → A[i][j] = ∑ k ∈ Finset.Iic j, L[i][k] * ~L[j][k] := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  obtain ⟨L₀, htri, hL₀⟩ := Any_And_Eq_Mul_Adjoint.of.PosDef hA
  have hlow₀ : ∀ i j, i < j → L₀ i j = 0 := fun i j hij => by
    simpa [getElem_getElem] using (htri j).1 i hij
  have hpos₀ : ∀ i, 0 < L₀ i i := fun i => by
    simpa [getElem_getElem] using (htri i).2
  have hrec₀ : IsCholeskyRec A L₀ := by
    rw [hL₀]
    apply IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0 hlow₀ hpos₀
  have hLL₀ : L = L₀ := by
    have key : ∀ j, ∀ i, L i j = L₀ i j := by
      intro j
      induction j using WellFoundedLT.induction with
      | _ j ih =>
        have hsum : ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2 = ∑ k ∈ Finset.Iio j, ‖L₀ j k‖ ^ 2 :=
          Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_Iio.mp hk) j]
        have hdiag : L j j = L₀ j j := by
          have hLjj : L j j = (A j j - ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2).sqrt := by
            have h := h₂ j j
            simp only [getElem_getElem] at h
            rw [ite_eq_right (lt_irrefl j), ite_true] at h
            simpa using h
          have h₀jj : L₀ j j =
              ↑(Real.sqrt (RCLike.re (A j j) - ∑ k ∈ Finset.Iio j, ‖L₀ j k‖ ^ 2)) := by
            have h := hrec₀ j j
            rw [ite_eq_right (lt_irrefl j), ite_eq_left rfl] at h
            simpa using h
          have him : RCLike.im (A j j) = 0 := by
            have hstar : star (A j j) = A j j := by
              have h := congr_fun (congr_fun h₀ j) j
              simpa [Matrix.conjTranspose_apply] using h
            rw [← RCLike.conj_eq_iff_im, ← RCLike.star_def]
            simpa using hstar
          have hpos : 0 < RCLike.re (A j j) - ∑ k ∈ Finset.Iio j, ‖L₀ j k‖ ^ 2 := by
            have h := hpos₀ j
            rw [h₀jj] at h
            exact Real.sqrt_pos.mp (RCLike.ofReal_pos.mp h)
          have hreal : A j j = ↑(RCLike.re (A j j)) := by
            rw [← RCLike.re_add_im (A j j), him]
            simp
          rw [hLjj, h₀jj, hsum, hreal]
          rw (config := { transparency := .default }) [RCLike.ofReal_re]
          have hsub : (↑(RCLike.re (A j j)) - ↑(∑ k ∈ Finset.Iio j, ‖L₀ j k‖ ^ 2) : ℂ) =
              ↑(RCLike.re (A j j) - ∑ k ∈ Finset.Iio j, ‖L₀ j k‖ ^ 2) :=
            (RCLike.ofReal_sub _ _).symm
          rw (config := { transparency := .default })
            [hsub, Complex.sqrt_of_nonneg (RCLike.ofReal_nonneg.mpr hpos.le)]
          congr 1
        intro i
        obtain hij | rfl | hij := lt_trichotomy j i
        ·
          have hs : ∑ k ∈ Finset.Iio j, L i k * star (L j k) =
              ∑ k ∈ Finset.Iio j, L₀ i k * star (L₀ j k) :=
            Finset.sum_congr rfl fun k hk => by
              rw [ih k (Finset.mem_Iio.mp hk) i, ih k (Finset.mem_Iio.mp hk) j]
          have hLij : L i j =
              (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j := by
            have hform := h₂ i j
            simp only [getElem_getElem] at hform
            rw [ite_eq_left hij] at hform
            simpa using hform
          have h₀ij : L₀ i j =
              (A i j - ∑ k ∈ Finset.Iio j, L₀ i k * star (L₀ j k)) / L₀ j j := by
            have hform := hrec₀ i j
            rw [ite_eq_left hij] at hform
            simpa using hform
          rw [hLij, h₀ij, hs, hdiag]
        · simpa using hdiag
        ·
          have hLij : L i j = 0 := by
            have hform := h₂ i j
            simp only [getElem_getElem] at hform
            rw [ite_eq_right (not_lt.mpr hij.le), ite_eq_right hij.ne'] at hform
            simpa using hform
          have h₀ij : L₀ i j = 0 := by
            have hform := hrec₀ i j
            rw [ite_eq_right (not_lt.mpr hij.le), ite_eq_right hij.ne'] at hform
            simpa using hform
          rw [hLij, h₀ij]
    ext i j
    simpa using key j i
  have hrec : IsCholeskyRec A L := by
    simpa [← hLL₀] using hrec₀
  obtain ⟨hlow, hpos, hL⟩ := All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef hA hrec
  have hs : ∀ i j : Fin n, A[i][j] = ∑ k ∈ Finset.Iic j, L[i][k] * ~L[j][k] := by
    intro i j
    simp only [getElem_getElem]
    rw [hL, GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0 hlow, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]
  intro i _
  refine ⟨hpos i, ?_, fun j _ => hs i j⟩
  rw [hs i i]
  simp only [RCLike.star_def, RCLike.mul_conj]
  push_cast
  rfl


-- created on 2023-05-01
-- updated on 2026-11-07
