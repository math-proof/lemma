import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α]
  {Φ : ContinuousSemiflow α}
  {K : Set α}
-- given
  (h₀ : IsClosed K)
  (h₁ : IsForwardInvariant Φ.toFun K) :
-- imply
  omegaLimit atTop Φ.toFun K ⊆ K := by
-- proof
  intro y hy
  refine closure_minimal ?_ h₀ ((OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici Φ.toFun K y).1 hy 0)
  rintro _ ⟨t, ht, x, hx, rfl⟩
  exact h₁ ht hx


-- created on 2026-09-26
