import Mathlib
import sympy.Basic


/--
[IharaLemma_resInj_of_reduction](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_resInj_of_reduction.lean)
-/
@[main]
private lemma main
  [CommRing R]
  {V L Vk Lk : Type*} [AddCommGroup V] [Module R V] [AddCommGroup L] [Module R L] [AddCommGroup Vk] [Module R Vk] [AddCommGroup Lk] [Module R Lk]
  {ϖ : R}
  {f : V →ₗ[R] L}
  {redV : V →ₗ[R] Vk}
  {redL : L →ₗ[R] Lk}
  {fk : Vk →ₗ[R] Lk}
-- given
  (hsq : ∀ v, redL (f v) = fk (redV v))
  (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁)
  (hϖ : ∀ x : L, redL (ϖ • x) = 0)
  (hfk : Function.Injective fk) :
-- imply
  ∀ (v : V) (x : L), f v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁ := by
-- proof
  intro v x h
  apply hker
  apply hfk
  rw [← hsq, h, hϖ, map_zero]


-- created on 2026-10-05
