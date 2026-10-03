import Mathlib
import sympy.Basic


/--
[LinearMap_trace_eq_and_det_eq_of_semiconj](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_trace_eq_and_det_eq_of_semiconj.lean)
-/
@[main]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {f : Module.End R M}
  {g : Module.End R N}
-- given
  (e : M ≃ₗ[R] N)
  (h : ∀ x : M, e (f x) = g (e x)) :
-- imply
  LinearMap.trace R M f = LinearMap.trace R N g ∧ LinearMap.det f = LinearMap.det g := by
-- proof
  have hg : g = e.conj f := by
    ext y
    rw [LinearEquiv.conj_apply]
    simp [h]
  subst hg
  exact ⟨(LinearMap.trace_conj' f e).symm, (LinearMap.det_conj f e).symm⟩


-- created on 2026-10-03
