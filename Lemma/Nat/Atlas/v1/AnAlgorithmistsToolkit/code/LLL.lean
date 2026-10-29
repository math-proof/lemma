import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.LLL.Part2
open InnerProductSpace Finset LLL


namespace LLL

/--
[gramSchmidtVec_norm_sq_half](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LLL.lean)
-/
@[path]
lemma gramSchmidtVec_norm_sq_half
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  (b : Fin n → E)
  (hred : IsLLLReduced b)
  (i : Fin n)
  (hi : (i : ℕ) + 1 < n) :
-- imply
  ‖gramSchmidtVec b ⟨i + 1, hi⟩‖ ^ 2 ≥ 1 / 2 * ‖gramSchmidtVec b i‖ ^ 2 := by
-- proof
  have hlov := hred.lovász i hi
  set bstar_i := gramSchmidtVec b i
  set bstar_next := gramSchmidtVec b ⟨i + 1, hi⟩
  set μ := gramSchmidtCoeff b ⟨i + 1, hi⟩ i
  have hne : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≠ i := by
    intro h; have := congr_arg Fin.val h; simp at this
  have hortho : ⟪bstar_next, bstar_i⟫_ℝ = 0 :=
    gramSchmidt_orthogonal ℝ b hne
  have hexpand : ‖bstar_next + μ • bstar_i‖ ^ 2 =
    ‖bstar_next‖ ^ 2 + μ ^ 2 * ‖bstar_i‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hortho, mul_zero, mul_zero, add_zero,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hsize : |μ| ≤ 1 / 2 :=
    hred.size_reduced _ _ (Fin.mk_lt_mk.mpr (Nat.lt_succ_of_le le_rfl))
  have hmu_sq : μ ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs μ, abs_nonneg μ]
  rw [hexpand] at hlov
  nlinarith [sq_nonneg (‖bstar_i‖)]

end LLL

namespace LLL

/--
[gramSchmidtVec_norm_sq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LLL.lean)
-/
@[path]
lemma gramSchmidtVec_norm_sq_geometric
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {n : ℕ}
  {b : Fin (n + 1) → E}
  {j : ℕ}
-- given
  (hred : IsLLLReduced b)
  (hj : j < n + 1) :
-- imply
  ‖gramSchmidtVec b ⟨j, hj⟩‖ ^ 2 ≥ (1 / 2 : ℝ) ^ j * ‖gramSchmidtVec b 0‖ ^ 2 := by
-- proof
  induction j with
  | zero => simp
  | succ k ih =>
    have hk : k < n + 1 := by omega
    have h_half := gramSchmidtVec_norm_sq_half b hred ⟨k, hk⟩ (by omega)
    have h_ih := ih hk
    calc ‖gramSchmidtVec b ⟨k + 1, hj⟩‖ ^ 2
      ≥ 1 / 2 * ‖gramSchmidtVec b ⟨k, hk⟩‖ ^ 2 := h_half
      _ ≥ 1 / 2 * ((1 / 2 : ℝ) ^ k * ‖gramSchmidtVec b 0‖ ^ 2) := by gcongr
      _ = (1 / 2 : ℝ) ^ (k + 1) * ‖gramSchmidtVec b 0‖ ^ 2 := by rw [pow_succ]; ring

end LLL

namespace LLL

/--
[gramSchmidtVec_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LLL.lean)
-/
@[path]
lemma gramSchmidtVec_zero
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {n : ℕ}
  {b : Fin (n + 1) → E} :
-- imply
  gramSchmidtVec b 0 = b 0 := by
-- proof
  unfold gramSchmidtVec
  exact gramSchmidt_bot ℝ b

end LLL


-- created on 2026-10-23
