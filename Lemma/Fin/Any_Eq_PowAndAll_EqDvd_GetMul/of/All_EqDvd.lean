import Mathlib
import sympy.Basic

open scoped MatrixGroups ModularForm

/--
[ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq.lean)
-/
@[path]
private lemma main
  {M : ℕ} [NeZero M]
  {k : ℤ}
  {i : ℕ}
  {F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k}
-- given
  (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M → (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
-- imply
  ∃ P : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) ((i : ℤ) * k),
      (∀ t : ZMod M, (⇑(P t) : UpperHalfPlane → ℂ) = (⇑(F t) : UpperHalfPlane → ℂ) ^ i) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(P t) : UpperHalfPlane → ℂ) ∣[(i : ℤ) * k] γ = ⇑(P (t * ((γ 1 1 : ℤ) : ZMod M)))) := by
-- proof
  induction i with
  | zero =>
    rw [show ((0 : ℕ) : ℤ) * k = 0 by simp]
    refine ⟨fun _ => ModularForm.const 1, fun t => ?_, fun t γ _ => ?_⟩
    · rw [pow_zero]; rfl
    · have h := ModularForm.is_invariant_const γ (1 : ℂ)
      exact h
  | succ i ih =>
    obtain ⟨P, hP1, hP2⟩ := ih
    rw [show ((i + 1 : ℕ) : ℤ) * k = (i : ℤ) * k + k by push_cast; ring]
    refine ⟨fun t => (P t).mul (F t), fun t => ?_, fun t γ hγ => ?_⟩
    · rw [ModularForm.coe_mul, hP1, pow_succ]
    · simp only [ModularForm.coe_mul]
      rw [ModularForm.mul_slash_SL2, hP2 t γ hγ, hF t γ hγ]


-- created on 2026-10-05
