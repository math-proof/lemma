import Mathlib
import sympy.Basic

open scoped BigOperators

/--
[IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {A' : Type v} [CommRing A'] [Algebra A A']
  {M : Type w} [AddCommGroup M] [Module A M]
  {M' : Type w'} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
  {f : M →ₗ[A] M'}
  {n : ℕ}
  {x : Fin n → M}
  {φ : Fin n → (M →ₗ[A] A)}
-- given
  (hf : IsBaseChange A' f)
  (hxφ : ∀ m : M, ∑ i, φ i m • x i = m) :
-- imply
  ∃ φ' : Fin n → (M' →ₗ[A'] A'),
      (∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m)) ∧
        ∀ m' : M', ∑ i, φ' i m' • f (x i) = m' := by
-- proof
  let φ' : Fin n → (M' →ₗ[A'] A') := fun i => hf.lift ((Algebra.linearMap A A').comp (φ i))
  have hφ' : ∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m) := fun i m =>
    hf.lift_eq _ _
  refine ⟨φ', hφ', fun m' => ?_⟩
  induction m' using hf.inductionOn with
  | tmul m =>
      calc
        _ = ∑ i, f (φ i m • x i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hφ', algebraMap_smul, map_smul]
        _ = f m := by
          rw [← map_sum, hxφ]
  | smul s m' ih =>
      conv_rhs => rw [← ih]
      simp only [map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
  | add m₁ m₂ ih₁ ih₂ =>
      conv_rhs => rw [← ih₁, ← ih₂]
      simp only [map_add, add_smul, Finset.sum_add_distrib]


-- created on 2026-10-05
