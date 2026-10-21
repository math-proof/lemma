import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma eq_of_forall_mem_forall_mem_eval_eq {K : Type*} [CommRing K] [IsDomain K]
    (P Q : MvPolynomial (Fin 2) K) (S T : Set K) (hS : S.Infinite) (hT : T.Infinite)
    (h : ∀ x ∈ S, ∀ y ∈ T, MvPolynomial.eval ![x, y] P = MvPolynomial.eval ![x, y] Q) :
    P = Q := by
  refine MvPolynomial.funext_set ![S, T] (fun i => by fin_cases i <;> simpa) ?_
  intro v hv
  have h0 : v 0 ∈ S := by simpa using hv 0 (Set.mem_univ _)
  have h1 : v 1 ∈ T := by simpa using hv 1 (Set.mem_univ _)
  have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv']; exact h _ h0 _ h1
private lemma eq_zero_of_forall_mem_forall_mem_eval_eq_zero {K : Type*} [CommRing K] [IsDomain K]
    (P : MvPolynomial (Fin 2) K) (S T : Set K) (hS : S.Infinite) (hT : T.Infinite)
    (h : ∀ x ∈ S, ∀ y ∈ T, MvPolynomial.eval ![x, y] P = 0) :
    P = 0 :=
  eq_of_forall_mem_forall_mem_eval_eq P 0 S T hS hT (by simpa using h)
private lemma eq_of_forall_eval_rpow_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ) (hS : S.Infinite)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set f : ℝ → ℂ := fun u => (((N : ℝ) ^ u : ℝ) : ℂ) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have : (N : ℝ) ^ a = (N : ℝ) ^ b := by
      simpa [hf] using hab
    exact (Real.strictMono_rpow_of_base_gt_one hN').injective this
  have hT : (f '' Set.Ioi u₀).Infinite := (Set.Ioi_infinite u₀).image hfinj.injOn
  refine eq_of_forall_mem_forall_mem_eval_eq P Q S (f '' Set.Ioi u₀) hS hT ?_
  rintro x hx _ ⟨u, hu, rfl⟩
  exact h x hx u hu
private lemma eval_eq_eval_of_forall_eval_rpow_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    (∀ x y : ℂ, MvPolynomial.eval ![x, y] P = MvPolynomial.eval ![x, y] Q) ∧
      ∀ x : ℂ, MvPolynomial.eval ![x, 1] P = MvPolynomial.eval ![x, 1] Q := by
  obtain rfl := eq_of_forall_eval_rpow_eq N hN u₀ S hS P Q h
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩
/--
[MvPolynomial_eq_of_forall_eval_rpow_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPolynomial_eq_of_forall_eval_rpow_eq.lean)
-/
@[path]
private lemma main (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (S : Set ℂ)
    (hS : S.Infinite) (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ x ∈ S, ∀ u : ℝ, u₀ < u →
      MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q) :
    P = Q :=
  eq_of_forall_eval_rpow_eq N hN u₀ S hS P Q h

-- created on 2026-10-20
