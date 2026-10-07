import sympy.matrices.cholesky
import sympy.Basic
open Matrix
open scoped ComplexOrder


@[main]
private lemma main
  [RCLike 𝕜]
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) 𝕜}
-- given
  (hA : A.PosDef) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) 𝕜, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᴴ := by
-- proof
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
    ·
      intro b _ hb
      obtain h | h := lt_or_gt_of_ne hb
      · rw [hLi b i h, mul_zero]
      · rw [hLo i b h, zero_mul]
    ·
      intro h
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
  ·
    intro i j h
    rw [Matrix.mul_diagonal, hLo i j h, zero_mul]
  ·
    intro i
    have e : (Lo * diagonal c) i i = ((Real.sqrt (r i) * ‖Lo i i‖ : ℝ) : 𝕜) := by
      rw [Matrix.mul_diagonal]
      simp only [hc_def, RCLike.star_def]
      have hm : Lo i i * (starRingEnd 𝕜) (Lo i i) = (‖Lo i i‖ : 𝕜) ^ 2 := RCLike.mul_conj _
      push_cast
      calc _ = (Real.sqrt (r i) : 𝕜) * (Lo i i * (starRingEnd 𝕜) (Lo i i)) / (‖Lo i i‖ : 𝕜) := by ring
        _ = _ := by rw [hm, pow_two, ← mul_assoc, mul_div_assoc, div_self (hn i), mul_one]
    rw [e]
    exact RCLike.pos_iff_exists_ofReal.mpr ⟨_, mul_pos (Real.sqrt_pos.mpr (hr i)) (norm_pos_iff.mpr (hne i)), rfl⟩
  ·
    symm
    calc Lo * diagonal c * (Lo * diagonal c)ᴴ = Lo * diagonal (LDL.diagEntries hA) * Loᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, ← Matrix.mul_assoc, Matrix.mul_assoc Lo,
            Matrix.diagonal_mul_diagonal]
          congr 3
          funext j
          rw [Pi.star_apply, hcc j]
      _ = A := LDL.lower_conj_diag hA


-- created on 2026-10-07
