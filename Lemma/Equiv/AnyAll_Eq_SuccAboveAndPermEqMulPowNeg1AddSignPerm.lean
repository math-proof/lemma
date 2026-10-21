import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq.lean)
-/
@[path]
private lemma main
  {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
  -- imply
  ∃ τ : Equiv.Perm (Fin n), (∀ k : Fin n, σ (j.succAbove k) = (σ j).succAbove (τ k)) ∧ Equiv.Perm.sign σ = (-1) ^ ((j : ℕ) + ((σ j) : ℕ)) * Equiv.Perm.sign τ := by
  -- proof
  classical
  set σ' : Equiv.Perm (Fin (n + 1)) := Fin.cycleRange (σ j) * σ * (Fin.cycleRange j)⁻¹ with hσ'
  have hσ'0 : σ' 0 = 0 := by
    change Fin.cycleRange (σ j) (σ ((Fin.cycleRange j).symm 0)) = 0
    rw [Fin.cycleRange_symm_zero, Fin.cycleRange_self]
  set d := Equiv.Perm.decomposeFin σ' with hd
  have hσ'd : σ' = Equiv.Perm.decomposeFin.symm (d.1, d.2) := by
    rw [Prod.mk.eta, hd, Equiv.symm_apply_apply]
  have hd1 : d.1 = 0 := by
    have hzero := Equiv.Perm.decomposeFin_symm_apply_zero d.1 d.2
    rw [← hσ'd, hσ'0] at hzero
    apply hzero.symm
  have hsucc : ∀ x : Fin n, σ' x.succ = (d.2 x).succ := by
    intro x
    rw [hσ'd, Equiv.Perm.decomposeFin_symm_apply_succ, hd1, Equiv.swap_self, Equiv.refl_apply]
  refine ⟨d.2, fun k => ?_, ?_⟩
  ·
    have h1 : σ = (Fin.cycleRange (σ j))⁻¹ * σ' * Fin.cycleRange j := by
      rw [hσ']
      group
    conv_lhs => rw [h1]
    change (Fin.cycleRange (σ j)).symm (σ' (Fin.cycleRange j (j.succAbove k))) = (σ j).succAbove (d.2 k)
    rw [Fin.cycleRange_succAbove, hsucc, Fin.cycleRange_symm_succ]
  ·
    have hs : Equiv.Perm.sign σ' = Equiv.Perm.sign d.2 := by
      rw [hσ'd, Equiv.Perm.decomposeFin.symm_sign, hd1, ite_eq_left rfl, one_mul]
    have hs' : Equiv.Perm.sign σ' = (-1) ^ ((σ j : Fin (n + 1)) : ℕ) * Equiv.Perm.sign σ * (-1) ^ (j : ℕ) := by
      simp [hσ', Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Fin.sign_cycleRange]
    rw [hs'] at hs
    have hu : ∀ m : ℕ, ((-1 : ℤˣ) ^ m) * ((-1 : ℤˣ) ^ m) = 1 := fun m => Int.units_mul_self _
    calc
      _ = ((-1) ^ ((σ j : Fin (n + 1)) : ℕ) * (-1) ^ ((σ j : Fin (n + 1)) : ℕ)) * Equiv.Perm.sign σ * ((-1) ^ (j : ℕ) * (-1) ^ (j : ℕ)) := by
        rw [hu, hu, one_mul, mul_one]
      _ = (-1) ^ (j : ℕ) * (-1) ^ ((σ j : Fin (n + 1)) : ℕ) * ((-1) ^ ((σ j : Fin (n + 1)) : ℕ) * Equiv.Perm.sign σ * (-1) ^ (j : ℕ)) := by
        simp only [mul_comm, mul_assoc, mul_left_comm]
      _ = (-1) ^ ((j : ℕ) + ((σ j : Fin (n + 1)) : ℕ)) * Equiv.Perm.sign d.2 := by
        rw [hs]
        congr 1
        apply (pow_add _ _ _).symm


-- created on 2026-10-20
