import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped Polynomial.Bivariate


/--
[Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsStandardEtale_exists_forall_algHom_evalEval_eq_zero_and_ext_and_surj_and_repr.lean)
-/
@[path]
private lemma main
  {k : Type} [Field k]
  {A : Type} [CommRing A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Algebra.IsStandardEtale k[X] A] :
-- imply
  ∃ (x : A) (F G : k[X][Y]),
    (∀ τ : A →ₐ[k] k,
      (F.evalEval (τ (algebraMap k[X] A X)) (τ x) = 0) ∧
      (G.evalEval (τ (algebraMap k[X] A X)) (τ x) ≠ 0) ∧
      ((derivative F).evalEval (τ (algebraMap k[X] A X)) (τ x) ≠ 0)) ∧
    (∀ τ τ' : A →ₐ[k] k, τ (algebraMap k[X] A X) = τ' (algebraMap k[X] A X) → τ x = τ' x → τ = τ') ∧
    (∀ z w : k, F.evalEval z w = 0 → G.evalEval z w ≠ 0 →
      ∃ τ : A →ₐ[k] k, τ (algebraMap k[X] A X) = z ∧ τ x = w) ∧
    (∀ s : A, ∃ (h : k[X][Y]) (n : ℕ), ∀ τ : A →ₐ[k] k,
      τ s * (G.evalEval (τ (algebraMap k[X] A X)) (τ x)) ^ n =
        h.evalEval (τ (algebraMap k[X] A X)) (τ x)) := by
-- proof
  classical
  obtain ⟨P⟩ := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation :
    Nonempty (StandardEtalePresentation k[X] A))
  have hring : ∀ τ : A →ₐ[k] k, (τ : A →+* k).comp (algebraMap k[X] A) =
      evalRingHom (τ (algebraMap k[X] A X)) := by
    intro τ
    apply ringHom_ext
    ·
      intro a
      show τ (algebraMap k[X] A (C a)) = eval _ (C a)
      rw [eval_C, ← algebraMap_eq, ← IsScalarTower.algebraMap_apply, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
    ·
      show τ (algebraMap k[X] A X) = eval _ X
      rw [eval_X]
  have hev : ∀ (τ : A →ₐ[k] k) (q : k[X][Y]),
      τ (aeval P.x q) = q.evalEval (τ (algebraMap k[X] A X)) (τ P.x) := by
    intro τ q
    rw [aeval_def, show τ (eval₂ (algebraMap k[X] A) P.x q) = (τ : A →+* k) (eval₂ (algebraMap k[X] A) P.x q) from rfl,
      hom_eval₂, hring τ, eval₂_evalRingHom]
    rfl
  obtain ⟨hf0, hgU⟩ := P.hasMap
  refine ⟨P.x, P.f, P.g, ?_, ?_, ?_, ?_⟩
  ·
    intro τ
    refine ⟨?_, ?_, ?_⟩
    ·
      rw [← hev, hf0, map_zero]
    ·
      rw [← hev]
      apply (hgU.map τ).ne_zero
    ·
      rw [← hev]
      apply (P.hasMap.isUnit_derivative_f.map τ).ne_zero
  ·
    intro τ τ' hX hx
    let _ : Algebra k[X] k := (evalRingHom (τ (algebraMap k[X] A X))).toAlgebra
    let τR : A →ₐ[k[X]] k := {
      toRingHom := by
        exact (τ : A →+* k)
      commutes' := by
        intro p
        show ((τ : A →+* k).comp (algebraMap k[X] A)) p = _
        rw [hring τ]
        rfl
    }
    let τR' : A →ₐ[k[X]] k := {
      toRingHom := by
        exact (τ' : A →+* k)
      commutes' := by
        intro p
        show ((τ' : A →+* k).comp (algebraMap k[X] A)) p = _
        rw [hring τ', ← hX]
        rfl
    }
    have hcomp : τR.comp (P.equivRing.symm : P.Ring →ₐ[k[X]] A) =
        τR'.comp (P.equivRing.symm : P.Ring →ₐ[k[X]] A) := by
      apply StandardEtalePair.hom_ext
      show τ (P.equivRing.symm P.X) = τ' (P.equivRing.symm P.X)
      rw [P.equivRing_symm_X]
      apply hx
    apply AlgHom.ext
    intro s
    have := congrArg (fun φ : P.Ring →ₐ[k[X]] k => φ (P.equivRing s)) hcomp
    simp at this
    apply this
  ·
    intro z w hF hG
    let _ : Algebra k[X] k := (evalRingHom z).toAlgebra
    have haev : ∀ q : k[X][Y], aeval (R := k[X]) w q = q.evalEval z w := by
      intro q
      rw [aeval_def, show algebraMap k[X] k = evalRingHom z from rfl, eval₂_evalRingHom]
    have hmap : P.HasMap (S := k) w := by
      refine ⟨?_, ?_⟩
      ·
        rw [haev]
        apply hF
      ·
        apply isUnit_iff_ne_zero.mpr
        rw [haev]
        apply hG
    let ψ : P.Ring →ₐ[k[X]] k := P.lift w hmap
    let θ : A →ₐ[k[X]] k := ψ.comp (P.equivRing : A ≃ₐ[k[X]] P.Ring).toAlgHom
    let τ : A →ₐ[k] k := {
      toRingHom := by
        exact (θ : A →+* k)
      commutes' := by
        intro c
        show θ (algebraMap k A c) = c
        rw [IsScalarTower.algebraMap_apply k k[X] A, AlgHom.commutes]
        show eval z (algebraMap k k[X] c) = c
        rw [algebraMap_eq, eval_C]
    }
    refine ⟨τ, ?_, ?_⟩
    ·
      show θ (algebraMap k[X] A X) = z
      rw [AlgHom.commutes]
      show eval z X = z
      rw [eval_X]
    ·
      show ψ (P.equivRing P.x) = w
      rw [P.equivRing_x]
      apply P.lift_X w hmap
  ·
    intro s
    obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
    refine ⟨p, n, fun τ => ?_⟩
    have := congrArg τ hp
    rw [map_mul, map_pow, hev, hev] at this
    apply this


-- created on 2026-10-13
