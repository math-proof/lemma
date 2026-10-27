import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R]
  [Group Γ]
  [AddCommGroup T] [Module R T]
  (ρ : Γ →* Module.End R T)
  (I : Subgroup Γ)
  (f : T →ₗ[R] R)
  -- given
  (hI : I.Normal)
  (hf : ∀ τ ∈ I, LinearMap.comp f (ρ τ) = f) :
  -- imply
  ∃ M : Submodule R T, (∀ x : T, x ∈ M ↔ ∀ γ : Γ, f (ρ γ x) = 0) ∧ (∀ (γ : Γ) (x : T), x ∈ M → ρ γ x ∈ M) ∧ (∀ τ ∈ I, ∀ x : T, ρ τ x - x ∈ M) ∧ (∀ (r : R) (x : T), r ≠ 0 → r • x ∈ M → x ∈ M) ∧ (∀ x ∈ M, f x = 0) := by
  -- proof
  let M : Submodule R T :=
    { carrier := {x | ∀ γ : Γ, f (ρ γ x) = 0}
      add_mem' := by
        intro x y hx hy γ
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [map_add, map_add, hx γ, hy γ, add_zero]
      zero_mem' := by
        intro γ
        rw [map_zero, map_zero]
      smul_mem' := by
        intro r x hx γ
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [map_smul, map_smul, hx γ, smul_zero] }
  have hM : ∀ x : T, x ∈ M ↔ ∀ γ : Γ, f (ρ γ x) = 0 := fun x => Iff.rfl
  refine ⟨M, hM, ?_, ?_, ?_, ?_⟩
  ·
    intro γ x hx
    rw [hM] at hx ⊢
    intro γ'
    rw [← Module.End.mul_apply, ← map_mul]
    apply hx (γ' * γ)
  ·
    intro τ hτ x
    rw [hM]
    intro γ
    have hconj : γ * τ * γ⁻¹ ∈ I := hI.conj_mem τ hτ γ
    have h1 : ρ γ (ρ τ x) = ρ (γ * τ * γ⁻¹) (ρ γ x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    have h2 : f (ρ (γ * τ * γ⁻¹) (ρ γ x)) = f (ρ γ x) := by
      apply LinearMap.congr_fun (hf _ hconj) (ρ γ x)
    rw [map_sub, map_sub, h1, h2, sub_self]
  ·
    intro r x hr hx
    rw [hM] at hx ⊢
    intro γ
    have h := hx γ
    rw [map_smul, map_smul, smul_eq_mul] at h
    apply (mul_eq_zero.mp h).resolve_left hr
  ·
    intro x hx
    rw [hM] at hx
    simpa using hx 1


-- created on 2026-10-20
