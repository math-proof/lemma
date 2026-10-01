import Mathlib.Analysis.Matrix.LDL

/-! Cholesky decomposition: existence of a lower-triangular factor with positive diagonal
(from Mathlib's LDL decomposition) and uniqueness via the py Cholesky recursion `IsCholeskyRec`. -/

open Matrix
open scoped ComplexOrder

theorem Matrix.PosDef.exists_cholesky {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) :
    ∃ L : Matrix (Fin n) (Fin n) 𝕜, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᴴ := by
  set Li := LDL.lowerInv hA with hLi_def
  set Lo := LDL.lower hA with hLo_def
  have hLi : ∀ i j, i < j → Li i j = 0 := fun i j h => LDL.lowerInv_triangular hA h
  have hb : Matrix.BlockTriangular Li OrderDual.toDual := fun i j h => hLi i j (OrderDual.toDual_lt_toDual.mp h)
  have hLo : ∀ i j, i < j → Lo i j = 0 := by
    intro i j h
    exact Matrix.blockTriangular_inv_of_blockTriangular hb (OrderDual.toDual_lt_toDual.mpr h)
  have hdiag : ∀ i, Lo i i * Li i i = 1 := by
    intro i
    have h1 : Lo * Li = 1 := Matrix.inv_mul_of_invertible Li
    have := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at this
    · exact this
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hLi b i h, mul_zero]
      · rw [hLo i b h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hne : ∀ i, Lo i i ≠ 0 := by
    intro i h
    have := hdiag i
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hinj : Function.Injective Li.vecMul := by
    intro x y h
    have := congrArg (fun v => v ᵥ* Li⁻¹) h
    simpa [Matrix.vecMul_vecMul, Matrix.mul_inv_of_invertible] using this
  have hD : (LDL.diag hA).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hA.mul_mul_conjTranspose_same hinj
  have hd : ∀ i, 0 < LDL.diagEntries hA i := by
    intro i
    have := hD.diag_pos (i := i)
    simpa [LDL.diag] using this
  have : ∀ i, ∃ r : ℝ, 0 < r ∧ (r : 𝕜) = LDL.diagEntries hA i := fun i => RCLike.pos_iff_exists_ofReal.mp (hd i)
  choose r hr hrd using this
  set c : Fin n → 𝕜 := fun j => (Real.sqrt (r j) : 𝕜) * (star (Lo j j) / (‖Lo j j‖ : 𝕜)) with hc_def
  have hn : ∀ j, (‖Lo j j‖ : 𝕜) ≠ 0 := fun j => by
    rw [RCLike.ofReal_ne_zero, norm_ne_zero_iff]
    exact hne j
  have hcc : ∀ j, c j * star (c j) = LDL.diagEntries hA j := by
    intro j
    rw [← hrd j]
    simp only [hc_def, star_mul', star_div₀, RCLike.star_def, RCLike.conj_ofReal, RCLike.conj_conj]
    have hs : (Real.sqrt (r j) : 𝕜) * (Real.sqrt (r j) : 𝕜) = (r j : 𝕜) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hr j).le]
    have hm : (starRingEnd 𝕜) (Lo j j) * Lo j j = (‖Lo j j‖ : 𝕜) ^ 2 := RCLike.conj_mul _
    calc _ = ((Real.sqrt (r j) : 𝕜) * (Real.sqrt (r j) : 𝕜)) * ((starRingEnd 𝕜) (Lo j j) * Lo j j) / (‖Lo j j‖ : 𝕜) ^ 2 := by ring
      _ = (r j : 𝕜) := by rw [hs, hm, mul_div_assoc, div_self (pow_ne_zero 2 (hn j)), mul_one]
  refine ⟨Lo * diagonal c, ?_, ?_, ?_⟩
  · intro i j h
    rw [Matrix.mul_diagonal, hLo i j h, zero_mul]
  · intro i
    have e : (Lo * diagonal c) i i = ((Real.sqrt (r i) * ‖Lo i i‖ : ℝ) : 𝕜) := by
      rw [Matrix.mul_diagonal]
      simp only [hc_def, RCLike.star_def]
      have hm : Lo i i * (starRingEnd 𝕜) (Lo i i) = (‖Lo i i‖ : 𝕜) ^ 2 := RCLike.mul_conj _
      push_cast
      calc _ = (Real.sqrt (r i) : 𝕜) * (Lo i i * (starRingEnd 𝕜) (Lo i i)) / (‖Lo i i‖ : 𝕜) := by ring
        _ = _ := by rw [hm, pow_two, ← mul_assoc, mul_div_assoc, div_self (hn i), mul_one]
    rw [e]
    exact RCLike.pos_iff_exists_ofReal.mpr ⟨_, mul_pos (Real.sqrt_pos.mpr (hr i)) (norm_pos_iff.mpr (hne i)), rfl⟩
  · symm
    calc Lo * diagonal c * (Lo * diagonal c)ᴴ = Lo * diagonal (LDL.diagEntries hA) * Loᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, ← Matrix.mul_assoc, Matrix.mul_assoc Lo,
            Matrix.diagonal_mul_diagonal]
          congr 3
          funext j
          rw [Pi.star_apply, hcc j]
      _ = A := LDL.lower_conj_diag hA


/-- py `eq_piece` of the Cholesky algorithm:
`L[i, j] = (A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j]` for `j < i`,
`L[i, i] = sqrt(A[i, i] - ‖L[i, :i]‖²)`, and `0` above the diagonal. -/
def IsCholeskyRec {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (A L : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ i j, L i j =
    if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j
    else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : 𝕜)
    else 0

theorem Matrix.mul_conjTranspose_apply_of_lower {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {L : Matrix (Fin n) (Fin n) 𝕜}
    (hlow : ∀ i j, i < j → L i j = 0) (i j : Fin n) :
    (L * Lᴴ) i j = ∑ k ∈ Finset.Iio j, L i k * star (L j k) + L i j * star (L j j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic j)) (fun k _ hk => by
      rw [hlow j k (by simpa using hk), star_zero, mul_zero]),
    ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]

theorem IsCholeskyRec.of_factor {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {L : Matrix (Fin n) (Fin n) 𝕜}
    (hlow : ∀ i j, i < j → L i j = 0) (hpos : ∀ i, 0 < L i i) : IsCholeskyRec (L * Lᴴ) L := by
  have hst : ∀ j, star (L j j) = L j j := fun j => by
    rw [RCLike.star_def, RCLike.conj_eq_iff_im]
    exact (RCLike.pos_iff.mp (hpos j)).2
  intro i j
  rcases lt_trichotomy j i with h | rfl | h
  · rw [if_pos h, Matrix.mul_conjTranspose_apply_of_lower hlow, hst]
    have := (hpos j).ne'
    field_simp
    ring
  · rw [if_neg (lt_irrefl j), if_pos rfl, Matrix.mul_conjTranspose_apply_of_lower hlow]
    simp only [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_sum, ← RCLike.ofReal_add,
      RCLike.ofReal_re, add_sub_cancel_left, Real.sqrt_sq (norm_nonneg _)]
    obtain ⟨x, hx, hxz⟩ := RCLike.pos_iff_exists_ofReal.mp (hpos j)
    rw [← hxz, RCLike.norm_ofReal, abs_of_pos hx]
  · rw [if_neg (not_lt.mpr h.le), if_neg h.ne']
    exact hlow i j h

theorem IsCholeskyRec.eq {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {A L M : Matrix (Fin n) (Fin n) 𝕜}
    (h₁ : IsCholeskyRec A L) (h₂ : IsCholeskyRec A M) : L = M := by
  have key : ∀ j, ∀ i, L i j = M i j := by
    intro j
    induction j using WellFoundedLT.induction with
    | _ j ih =>
      have hdiag : L j j = M j j := by
        have hs : ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2 = ∑ k ∈ Finset.Iio j, ‖M j k‖ ^ 2 :=
          Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_Iio.mp hk) j]
        rw [h₁ j j, h₂ j j, if_neg (lt_irrefl j), if_pos rfl, if_neg (lt_irrefl j), if_pos rfl, hs]
      intro i
      rcases lt_trichotomy j i with h | rfl | h
      · have hs : ∑ k ∈ Finset.Iio j, L i k * star (L j k) = ∑ k ∈ Finset.Iio j, M i k * star (M j k) :=
          Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_Iio.mp hk) i, ih k (Finset.mem_Iio.mp hk) j]
        rw [h₁ i j, h₂ i j, if_pos h, if_pos h, hs, hdiag]
      · exact hdiag
      · rw [h₁ i j, h₂ i j, if_neg (not_lt.mpr h.le), if_neg h.ne', if_neg (not_lt.mpr h.le), if_neg h.ne']
  ext i j
  exact key j i

/-- The Cholesky recursion determines the factor: for positive definite `A`, a matrix satisfying the
recursion is lower triangular with positive diagonal and `A = L Lᴴ`. -/
theorem Matrix.PosDef.cholesky_of_rec {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {A L : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) (h : IsCholeskyRec A L) :
    (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᴴ := by
  obtain ⟨L₀, hlow, hpos, hL₀⟩ := hA.exists_cholesky
  have h₀ : IsCholeskyRec A L₀ := by
    rw [hL₀]
    exact IsCholeskyRec.of_factor hlow hpos
  rw [h.eq h₀]
  exact ⟨hlow, hpos, hL₀⟩

/-- One step of the Cholesky induction: if rows `< t` of `L` already satisfy the Cholesky relations
and `L` satisfies the off-diagonal recursion, then row `t` satisfies the off-diagonal relations and
the diagonal radicand `A t t - ‖L[t, :t]‖²` is positive. -/
theorem Matrix.PosDef.cholesky_step {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {A L : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef)
    (hpiece : ∀ i j, j < i → L i j = (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j)
    (t : Fin n)
    (hind : ∀ i, i < t → A i i = ((∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 : ℝ) : 𝕜) ∧ 0 < L i i ∧
      ∀ j, j < i → A i j = ∑ k ∈ Finset.Iic j, L i k * star (L j k)) :
    ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 : ℝ) : 𝕜) < A t t ∧
      ∀ j, j < t → A t j = ∑ k ∈ Finset.Iic j, L t k * star (L j k) := by
  have hst : ∀ j, j < t → star (L j j) = L j j := fun j hj => by
    rw [RCLike.star_def, RCLike.conj_eq_iff_im]
    exact (RCLike.pos_iff.mp (hind j hj).2.1).2
  refine ⟨?_, fun j hj => ?_⟩
  · obtain ⟨L₀, hlow, hpos, hL₀⟩ := hA.exists_cholesky
    have h₀rec : IsCholeskyRec A L₀ := by
      rw [hL₀]
      exact IsCholeskyRec.of_factor hlow hpos
    have claim : ∀ j, j < t → ∀ i, j ≤ i → i ≤ t → L i j = L₀ i j := by
      intro j
      induction j using WellFoundedLT.induction with
      | _ j ih =>
        intro hjt
        have hdiag : L j j = L₀ j j := by
          have e1 : RCLike.re (A j j) = ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2 + ‖L j j‖ ^ 2 := by
            rw [(hind j hjt).1, RCLike.ofReal_re, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]
          have hs : ∑ k ∈ Finset.Iio j, ‖L₀ j k‖ ^ 2 = ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2 :=
            Finset.sum_congr rfl fun k hk => by
              rw [ih k (Finset.mem_Iio.mp hk) (lt_trans (Finset.mem_Iio.mp hk) hjt) j (le_of_lt (Finset.mem_Iio.mp hk)) hjt.le]
          rw [h₀rec j j, if_neg (lt_irrefl j), if_pos rfl, hs, e1, add_sub_cancel_left, Real.sqrt_sq (norm_nonneg _)]
          obtain ⟨x, hx, hxz⟩ := RCLike.pos_iff_exists_ofReal.mp (hind j hjt).2.1
          rw [← hxz, RCLike.norm_ofReal, abs_of_pos hx]
        intro i hji hit
        rcases hji.lt_or_eq with hji | rfl
        · have hS : ∑ k ∈ Finset.Iio j, L i k * star (L j k) = ∑ k ∈ Finset.Iio j, L₀ i k * star (L₀ j k) :=
            Finset.sum_congr rfl fun k hk => by
              have hk' := Finset.mem_Iio.mp hk
              rw [ih k hk' (lt_trans hk' hjt) i (le_of_lt (lt_trans hk' hji)) hit,
                ih k hk' (lt_trans hk' hjt) j hk'.le hjt.le]
          rw [hpiece i j hji, h₀rec i j, if_pos hji, hS, hdiag]
        · exact hdiag
    have hAt : A t t = ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 + ‖L₀ t t‖ ^ 2 : ℝ) : 𝕜) := by
      have hs : ∑ k ∈ Finset.Iio t, L₀ t k * star (L₀ t k) = ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 : ℝ) : 𝕜) := by
        push_cast
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [← claim k (Finset.mem_Iio.mp hk) t (le_of_lt (Finset.mem_Iio.mp hk)) le_rfl, RCLike.star_def, RCLike.mul_conj]
      rw [hL₀, Matrix.mul_conjTranspose_apply_of_lower hlow, hs, RCLike.star_def, RCLike.mul_conj]
      push_cast
      ring
    rw [hAt, RCLike.ofReal_lt_ofReal]
    exact lt_add_of_pos_right _ (pow_pos (norm_pos_iff.mpr (hpos t).ne') 2)
  · rw [← Finset.Iio_insert, Finset.sum_insert (by simp), hpiece t j hj, hst j hj]
    have := (hind j hj).2.1.ne'
    field_simp
    ring


-- created on 2026-09-27
