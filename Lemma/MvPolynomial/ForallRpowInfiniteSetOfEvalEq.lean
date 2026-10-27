import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma eq_of_forall_mem_forall_mem_eval_eq [CommRing K] [IsDomain K] (P Q : MvPolynomial (Fin 2) K) (S T : Set K) (hS : S.Infinite) (hT : T.Infinite) (h : ∀ x ∈ S, ∀ y ∈ T, MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons y Matrix.vecEmpty)) P = MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons y Matrix.vecEmpty)) Q) : P = Q := by
  refine MvPolynomial.funext_set (Matrix.vecCons S (Matrix.vecCons T Matrix.vecEmpty)) (fun i => by fin_cases i <;> simpa) ?_
  intro v hv
  have h0 : v 0 ∈ S := by simpa using hv 0 (Set.mem_univ _)
  have h1 : v 1 ∈ T := by simpa using hv 1 (Set.mem_univ _)
  have hv' : v = Matrix.vecCons (v 0) (Matrix.vecCons (v 1) Matrix.vecEmpty) := by ext i; fin_cases i <;> rfl
  rw [hv']
  apply h _ h0 _ h1
private lemma eval_aeval_X_C_eq_eval [CommRing K] (P : MvPolynomial (Fin 2) K) (x y : K) : Polynomial.eval x (MvPolynomial.aeval (Matrix.vecCons Polynomial.X (Matrix.vecCons (Polynomial.C y) Matrix.vecEmpty)) P) = MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons y Matrix.vecEmpty)) P := by
  have key : (Polynomial.evalRingHom x).comp (MvPolynomial.aeval (Matrix.vecCons Polynomial.X (Matrix.vecCons (Polynomial.C y) Matrix.vecEmpty)) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K).toRingHom = MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons y Matrix.vecEmpty)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    ·
      simp
    ·
      fin_cases i <;> simp
  refine congrArg (fun f : MvPolynomial (Fin 2) K →+* K => f P) key
private lemma eq_of_forall_mem_infinite_setOf_eval_eq [CommRing K] [IsDomain K] [Infinite K] (P Q : MvPolynomial (Fin 2) K) (T : Set K) (hT : T.Infinite) (h : ∀ y ∈ T, Set.Infinite {x : K | MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons y Matrix.vecEmpty)) P = MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons y Matrix.vecEmpty)) Q}) : P = Q := by
  refine eq_of_forall_mem_forall_mem_eval_eq P Q Set.univ T Set.infinite_univ hT ?_
  intro x _ y hy
  have hxy : MvPolynomial.aeval (Matrix.vecCons Polynomial.X (Matrix.vecCons (Polynomial.C y) Matrix.vecEmpty)) P = MvPolynomial.aeval (Matrix.vecCons Polynomial.X (Matrix.vecCons (Polynomial.C y) Matrix.vecEmpty)) Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (h y hy).mono ?_
    intro x' hx'
    simpa only [Set.mem_ofPred_eq, eval_aeval_X_C_eq_eval] using hx'
  have := congrArg (Polynomial.eval x) hxy
  simpa only [eval_aeval_X_C_eq_eval] using this
private lemma eq_of_forall_rpow_infinite_setOf_eval_eq (N : ℕ) (hN : 1 < N) (u₀ : ℝ) (P Q : MvPolynomial (Fin 2) ℂ) (h : ∀ u : ℝ, u₀ < u → Set.Infinite {x : ℂ | MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons (((N : ℝ) ^ u : ℝ) : ℂ) Matrix.vecEmpty)) P = MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons (((N : ℝ) ^ u : ℝ) : ℂ) Matrix.vecEmpty)) Q}) : P = Q := by
  have hN' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set f : ℝ → ℂ := fun u => (((N : ℝ) ^ u : ℝ) : ℂ) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have : (N : ℝ) ^ a = (N : ℝ) ^ b := by
      simpa [hf] using hab
    refine (Real.strictMono_rpow_of_base_gt_one hN').injective this
  have hT : (f '' Set.Ioi u₀).Infinite := (Set.Ioi_infinite u₀).image hfinj.injOn
  refine eq_of_forall_mem_infinite_setOf_eval_eq P Q (f '' Set.Ioi u₀) hT ?_
  rintro _ ⟨u, hu, rfl⟩
  apply h u hu
/--
[MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPolynomial_eq_of_forall_rpow_infinite_setOf_eval_eq.lean)
-/
@[path]
private lemma main
  (N : ℕ) (hN : 1 < N) (u₀ : ℝ)
  (P Q : MvPolynomial (Fin 2) ℂ)
  (h : ∀ u : ℝ, u₀ < u → Set.Infinite {x : ℂ | MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons (((N : ℝ) ^ u : ℝ) : ℂ) Matrix.vecEmpty)) P = MvPolynomial.eval (Matrix.vecCons x (Matrix.vecCons (((N : ℝ) ^ u : ℝ) : ℂ) Matrix.vecEmpty)) Q}) :
  -- imply
  P = Q := eq_of_forall_rpow_infinite_setOf_eval_eq N hN u₀ P Q h


-- created on 2026-10-20
