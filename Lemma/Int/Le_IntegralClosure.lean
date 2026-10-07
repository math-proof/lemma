import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[HopfOrder_le_integralClosure_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfOrder_le_integralClosure_of_finite.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type w} [CommRing A] [Algebra R A]
  {S : Subalgebra R A} [Module.Finite R S] :
-- imply
  S ≤ integralClosure R A := by
-- proof
  intro x hx
  rw [mem_integralClosure_iff]
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have h : IsIntegral R (⟨x, hx⟩ : S) := Algebra.IsIntegral.isIntegral _
  exact h.map S.val


-- created on 2026-10-05
