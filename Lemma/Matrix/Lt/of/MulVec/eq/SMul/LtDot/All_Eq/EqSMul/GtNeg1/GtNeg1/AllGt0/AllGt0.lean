import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import sympy.Basic

open scoped Matrix


/--
Okishio's theorem (PF-free layer).
- `hM` : the old equilibrium `(1 + r) • (p ᵥ* M) = p` with strictly positive price vector `p`;
- `hcol`, `hi` : cost-reducing technical change in sector `i`, i.e. only column `i` of `M` changes and `p ⬝ᵥ M' col i < p ⬝ᵥ M col i`;
- `hMq` : `q'` is a strictly positive right eigenvector of the new matrix `M'` with eigenvalue `1 / (1 + r')` (the only Perron-Frobenius input).

Then the profit rate strictly rises: `r < r'`.
-/
@[path]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {M M' : Matrix S S ℝ}
  {p q' : S → ℝ}
  {r r' : ℝ}
  {i : S}
-- given
  (hp : ∀ k, 0 < p k)
  (hq : ∀ k, 0 < q' k)
  (hr : -1 < r)
  (hr' : -1 < r')
  (hM : (1 + r) • (p ᵥ* M) = p)
  (hcol : ∀ j, j ≠ i → ∀ k, M' k j = M k j)
  (hi : p ⬝ᵥ (fun k => M' k i) < p ⬝ᵥ (fun k => M k i))
  (hMq : M' *ᵥ q' = (1 / (1 + r')) • q') :
-- imply
  r < r' := by
-- proof
  have h₀ : 0 < 1 + r := by linarith
  have h₀' : 0 < 1 + r' := by linarith
  have hpM : p ᵥ* M = (1 / (1 + r)) • p := by
    calc
      _ = (1 / (1 + r)) • ((1 + r) • (p ᵥ* M)) := by
        rw [smul_smul]
        field_simp
        simp
      _ = _ := by rw [hM]
  have hle : ∀ j, (p ᵥ* M') j ≤ (p ᵥ* M) j := by
    intro j
    if hj : j = i then
      subst hj
      exact hi.le
    else
      apply le_of_eq
      simp only [Matrix.vecMul, dotProduct, hcol j hj]
  have hlt : (p ᵥ* M') i < (p ᵥ* M) i := hi
  have hpq : 0 < p ⬝ᵥ q' := by
    apply Finset.sum_pos (fun k _ => mul_pos (hp k) (hq k)) ⟨i, Finset.mem_univ i⟩
  have hd : 0 < ∑ j, ((p ᵥ* M) j - (p ᵥ* M') j) * q' j := by
    apply Finset.sum_pos' (fun j _ => mul_nonneg (sub_nonneg.mpr (hle j)) (hq j).le)
    exact ⟨i, Finset.mem_univ i, mul_pos (sub_pos.mpr hlt) (hq i)⟩
  have h₁ : ∑ j, ((p ᵥ* M) j - (p ᵥ* M') j) * q' j = (1 / (1 + r) - 1 / (1 + r')) * (p ⬝ᵥ q') := by
    calc
      _ = (p ᵥ* M) ⬝ᵥ q' - (p ᵥ* M') ⬝ᵥ q' := by
        simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
      _ = (1 / (1 + r)) * (p ⬝ᵥ q') - p ⬝ᵥ (M' *ᵥ q') := by
        rw [hpM, Matrix.dotProduct_mulVec, smul_dotProduct]
        rfl
      _ = _ := by
        rw [hMq, dotProduct_smul]
        simp only [smul_eq_mul]
        ring
  rw [h₁] at hd
  have h₂ : 1 / (1 + r') < 1 / (1 + r) := by
    have := (mul_pos_iff_of_pos_right hpq).mp hd
    linarith
  have := (one_div_lt_one_div h₀' h₀).mp h₂
  linarith


-- created on 2026-09-29