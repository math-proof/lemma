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
private lemma eval_aeval_X_C_eq_eval {K : Type*} [CommRing K] (P : MvPolynomial (Fin 2) K) (x y : K) :
    Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] P) =
      MvPolynomial.eval ![x, y] P := by
  have key : (Polynomial.evalRingHom x).comp
      (MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] :
        MvPolynomial (Fin 2) K →ₐ[K] Polynomial K).toRingHom = MvPolynomial.eval ![x, y] := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp
    · fin_cases i <;> simp
  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* K => f P) key
private lemma eq_of_forall_mem_infinite_setOf_eval_eq {K : Type*} [CommRing K] [IsDomain K]
    [Infinite K] (P Q : MvPolynomial (Fin 2) K) (T : Set K) (hT : T.Infinite)
    (h : ∀ y ∈ T, Set.Infinite {x : K | MvPolynomial.eval ![x, y] P = MvPolynomial.eval ![x, y] Q}) :
    P = Q := by
  refine eq_of_forall_mem_forall_mem_eval_eq P Q Set.univ T Set.infinite_univ hT ?_
  intro x _ y hy
  have hxy : MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] P =
      MvPolynomial.aeval ![Polynomial.X, Polynomial.C y] Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (h y hy).mono ?_
    intro x' hx'
    simpa only [Set.mem_setOf_eq, eval_aeval_X_C_eq_eval] using hx'
  have := congrArg (Polynomial.eval x) hxy
  simpa only [eval_aeval_X_C_eq_eval] using this
private lemma eq_of_forall_rpow_infinite_setOf_eval_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ u : ℝ, u₀ < u →
      Set.Infinite {x : ℂ | MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q}) :
    P = Q := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set f : ℝ → ℂ := fun u => (((N : ℝ) ^ u : ℝ) : ℂ) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have : (N : ℝ) ^ a = (N : ℝ) ^ b := by
      simpa [hf] using hab
    exact (Real.strictMono_rpow_of_base_gt_one hN').injective this
  have hT : (f '' Set.Ioi u₀).Infinite := (Set.Ioi_infinite u₀).image hfinj.injOn
  refine eq_of_forall_mem_infinite_setOf_eval_eq P Q (f '' Set.Ioi u₀) hT ?_
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu
/--
[MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq.lean)
-/
@[path]
private lemma main (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (h : ∀ u : ℝ, u₀ < u →
      Set.Infinite {x : ℂ | MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] P =
        MvPolynomial.eval ![x, (((N : ℝ) ^ u : ℝ) : ℂ)] Q}) :
    P = Q :=
  eq_of_forall_rpow_infinite_setOf_eval_eq N hN u₀ P Q h

-- created on 2026-10-20
