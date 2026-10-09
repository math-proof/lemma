import Mathlib
import sympy.Basic

open Polynomial

/--
[AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq.lean)
-/
@[path]
private lemma main
  {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  {g : F}
-- given
  (hg : g ∉ Set.range (algebraMap K F)) :
-- imply
  ∃ φ : RatFunc K →ₐ[K] F, φ RatFunc.X = g := by
-- proof
  have htr : Transcendental K g := by
    intro halg
    apply hg
    have hint : IsIntegral K g := halg.isIntegral
    have hdeg : (minpoly K g).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
    exact ⟨a, ha⟩
  have hinj : Function.Injective (Polynomial.aeval (R := K) g) :=
    transcendental_iff_injective.mp htr
  refine ⟨RatFunc.liftAlgHom (Polynomial.aeval g) ?_, ?_⟩
  · intro p hp
    simp only [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  · rw [RatFunc.liftAlgHom_apply]
    simp


-- created on 2026-10-05
