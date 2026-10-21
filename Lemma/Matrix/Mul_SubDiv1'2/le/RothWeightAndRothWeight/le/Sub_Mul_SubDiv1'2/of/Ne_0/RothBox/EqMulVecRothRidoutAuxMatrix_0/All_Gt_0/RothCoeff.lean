import Lemma.Matrix.Eq_0.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open Matrix
open scoped Matrix


/--
[roth_ridout_coeff_weight_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α : ℝ}
  {m : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
  {c : RothCoeff r}
  {j : RothBox r}
-- given
  (hr : ∀ h, 0 < r h)
  (hker : Matrix.mulVec (rothRidoutAuxMatrix α r γ) c = 0)
  (hc : c j ≠ 0) :
-- imply
  (m : ℝ) * (1 / 2 - γ) ≤ rothWeight r (fun h ↦ j h) ∧
    rothWeight r (fun h ↦ j h) ≤
      (m : ℝ) - (m : ℝ) * (1 / 2 - γ) := by
-- proof
  let T : ℝ := (m : ℝ) * (1 / 2 - γ)
  change T ≤ rothWeight r (fun h ↦ j h) ∧
    rothWeight r (fun h ↦ j h) ≤ (m : ℝ) - T
  have hcomp_weight :
    rothWeight r (fun h ↦ rothRidoutBoxComplement r j h) =
      (m : ℝ) - rothWeight r (fun h ↦ j h) := calc
    _ = ∑ h, (1 - (j h : ℝ) / r h) := by
      unfold rothWeight
      apply Finset.sum_congr rfl
      intro h _
      change (((rothRidoutBoxComplement r j) h : ℕ) : ℝ) / r h =
        1 - (j h : ℝ) / r h
      change ((r h - j h : ℕ) : ℝ) / r h = 1 - (j h : ℝ) / r h
      rw [Nat.cast_sub (Nat.le_of_lt_succ (j h).isLt)]
      have hr0 : (r h : ℝ) ≠ 0 := by exact_mod_cast (hr h).ne'
      field_simp
    _ = (m : ℝ) - rothWeight r (fun h ↦ j h) := by
      rw [Finset.sum_sub_distrib]
      simp [rothWeight]
  have hinvolutive : rothRidoutBoxComplement r (rothRidoutBoxComplement r j) = j := by
    funext h
    apply Fin.ext
    change r h - (r h - j h) = j h
    have hj : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  constructor
  ·
    apply le_of_not_gt
    intro hj
    have hjlow : j ∈ rothLowIndices r γ := by
      simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [T] using hj
    apply hc
    apply Eq_0.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff hker ⟨j, hjlow⟩
  ·
    apply le_of_not_gt
    intro hj
    have hcomp : rothWeight r (fun h ↦ rothRidoutBoxComplement r j h) < T := by
      rw [hcomp_weight]
      linarith
    have hcomplow : rothRidoutBoxComplement r j ∈ rothLowIndices r γ := by
      simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [T] using hcomp
    have hz := Eq_0.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff.complement hker
      ⟨rothRidoutBoxComplement r j, hcomplow⟩
    rw [hinvolutive] at hz
    apply hc
    apply hz


-- created on 2026-10-21
