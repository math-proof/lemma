import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Algebra_trace_baseChange_one_tmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_trace_baseChange_one_tmul.lean)
-/

private lemma  trace_baseChange_one_tmul
    {A B : Type*}
    [CommRing A]
    [CommRing B]
    [Algebra A B]
    (S : Type*)
    [CommRing S]
    [Algebra A S]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    Algebra.trace S (S ⊗[A] B) (1 ⊗ₜ x) = algebraMap A S (Algebra.trace A B x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine TensorProduct.AlgebraTensorModule.ext fun s y => ?_
  change (1 ⊗ₜ[A] x) * (s ⊗ₜ[A] y) = LinearMap.baseChange S (Algebra.lmul A B x) (s ⊗ₜ[A] y)
  rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
@[path]
private lemma main
  [CommRing S]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A S] [Module.Free A B] [Module.Finite A B]
  {x : B} :
-- imply
  Algebra.trace S (TensorProduct A S B) (1 ⊗ₜ[A] x) = algebraMap A S (Algebra.trace A B x) :=
-- proof
  trace_baseChange_one_tmul S x


-- created on 2026-10-05
