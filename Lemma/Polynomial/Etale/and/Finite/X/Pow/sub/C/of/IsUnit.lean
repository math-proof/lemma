import sympy.Basic
import sympy.Flt
import Mathlib

open Polynomial

/--
[AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
-- given
  (n : ℕ) (u : R) (hn : IsUnit (n : R)) (hu : IsUnit u) :
-- imply
  Algebra.Etale R (AdjoinRoot (X ^ n - C u : R[X])) ∧
      Module.Finite R (AdjoinRoot (X ^ n - C u : R[X])) := by
-- proof
  obtain hR | hR := subsingleton_or_nontrivial R
  ·
    have : Subsingleton (AdjoinRoot (X ^ n - C u : R[X])) :=
      (algebraMap R (AdjoinRoot (X ^ n - C u : R[X]))).codomain_trivial
    refine ⟨?_, ?_⟩
    ·
      exact Algebra.Etale.of_equiv
        ((AlgEquiv.ofBijective (Algebra.ofId R (AdjoinRoot (X ^ n - C u : R[X])))
          ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩))
    ·
      exact Module.Finite.of_surjective (Algebra.linearMap R _)
        (fun y => ⟨0, Subsingleton.elim _ _⟩)
  ·
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have : Algebra.IsStandardEtale R (AdjoinRoot (X ^ n - C u : R[X])) :=
      isStandardEtale n u hn0 hn hu
    exact ⟨inferInstance, (monic_X_pow_sub_C u hn0).finite_adjoinRoot⟩

-- created on 2026-10-09
