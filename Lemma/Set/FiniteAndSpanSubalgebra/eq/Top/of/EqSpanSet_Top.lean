import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[HopfOrder_finite_sup_and_span_sup_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfOrder_finite_sup_and_span_sup_eq_top.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {K : Type v} [Field K] [Algebra R K]
  {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
  {S S' : Subalgebra R A} [Module.Finite R S] [Module.Finite R S']
-- given
  (hspan : Submodule.span K (S : Set A) = ⊤) :
-- imply
  Module.Finite R ↥(S ⊔ S') ∧ Submodule.span K ((S ⊔ S' : Subalgebra R A) : Set A) = ⊤ := by
-- proof
  refine ⟨Subalgebra.finite_sup S S', ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← hspan]
  exact Submodule.span_mono (fun x hx => (le_sup_left : S ≤ S ⊔ S') hx)


-- created on 2026-10-05
