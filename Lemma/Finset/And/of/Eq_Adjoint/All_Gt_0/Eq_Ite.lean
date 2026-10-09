import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0
import Lemma.Matrix.All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef
open Matrix
open scoped ComplexOrder


@[path]
private lemma l11
  {n : ℕ}
  {A L : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin (n + 3) → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : ℂ) else 0) :
-- imply
  A 1 0 = L 0 0 * L 1 0 ∧ 0 < L 1 1 ∧ A 1 1 = ((‖L 1 0‖ ^ 2 + ‖L 1 1‖ ^ 2 : ℝ) : ℂ) := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  obtain ⟨hlow, hpos, hL⟩ := All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef hA h₂
  have hst : ∀ j, star (L j j) = L j j := fun j => by
    rw [RCLike.star_def, RCLike.conj_eq_iff_im]
    exact (RCLike.pos_iff.mp (hpos j)).2
  have e : ∀ i j, A i j = ∑ k ∈ Finset.Iio j, L i k * star (L j k) + L i j * star (L j j) := fun i j => by
    rw [hL, GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0 hlow]
  have i0 : Finset.Iio (0 : Fin (n + 3)) = ∅ := by
    ext k
    simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt]
    exact Fin.zero_le k
  have i1 : Finset.Iio (1 : Fin (n + 3)) = {0} := by
    ext k
    simp only [Finset.mem_Iio, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff, Fin.val_one, Fin.val_zero]
    omega
  refine ⟨?_, hpos 1, ?_⟩
  ·
    rw [e, i0, Finset.sum_empty, zero_add, hst, mul_comm]
  ·
    rw [e, i1, Finset.sum_singleton]
    simp only [RCLike.star_def, RCLike.mul_conj]
    push_cast
    rfl


@[path]
private lemma l00
  {n : ℕ}
  {A L : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin (n + 3) → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : ℂ) else 0) :
-- imply
  0 < L 0 0 ∧ A 0 0 = L 0 0 ^ 2 := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  obtain ⟨hlow, hpos, hL⟩ := All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef hA h₂
  have hst : ∀ j, star (L j j) = L j j := fun j => by
    rw [RCLike.star_def, RCLike.conj_eq_iff_im]
    exact (RCLike.pos_iff.mp (hpos j)).2
  have e : ∀ i j, A i j = ∑ k ∈ Finset.Iio j, L i k * star (L j k) + L i j * star (L j j) := fun i j => by
    rw [hL, GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0 hlow]
  have i0 : Finset.Iio (0 : Fin (n + 3)) = ∅ := by
    ext k
    simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt]
    exact Fin.zero_le k
  refine ⟨hpos 0, ?_⟩
  rw [e, i0, Finset.sum_empty, zero_add, hst, sq]


@[path]
private lemma l22
  {n : ℕ}
  {A L : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin (n + 3) → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : ℂ) else 0) :
-- imply
  A 2 0 = L 0 0 * L 2 0 ∧ A 2 1 = star (L 1 0) * L 2 0 + L 1 1 * L 2 1 ∧ 0 < L 2 2 ∧ A 2 2 = ((‖L 2 0‖ ^ 2 + ‖L 2 1‖ ^ 2 + ‖L 2 2‖ ^ 2 : ℝ) : ℂ) := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  obtain ⟨hlow, hpos, hL⟩ := All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef hA h₂
  have hst : ∀ j, star (L j j) = L j j := fun j => by
    rw [RCLike.star_def, RCLike.conj_eq_iff_im]
    exact (RCLike.pos_iff.mp (hpos j)).2
  have e : ∀ i j, A i j = ∑ k ∈ Finset.Iio j, L i k * star (L j k) + L i j * star (L j j) := fun i j => by
    rw [hL, GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0 hlow]
  have i0 : Finset.Iio (0 : Fin (n + 3)) = ∅ := by
    ext k
    simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt]
    exact Fin.zero_le k
  have i1 : Finset.Iio (1 : Fin (n + 3)) = {0} := by
    ext k
    simp only [Finset.mem_Iio, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff, Fin.val_one, Fin.val_zero]
    omega
  have i2 : Finset.Iio (2 : Fin (n + 3)) = {0, 1} := by
    ext k
    simp only [Finset.mem_Iio, Finset.mem_insert, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff, Fin.val_one, Fin.val_zero, Fin.val_two]
    omega
  refine ⟨?_, ?_, hpos 2, ?_⟩
  ·
    rw [e, i0, Finset.sum_empty, zero_add, hst, mul_comm]
  ·
    rw [e, i1, Finset.sum_singleton, hst]
    ring
  ·
    rw [e, i2, Finset.sum_pair (by simp)]
    simp only [RCLike.star_def, RCLike.mul_conj]
    push_cast
    rfl


-- created on 2023-05-02
