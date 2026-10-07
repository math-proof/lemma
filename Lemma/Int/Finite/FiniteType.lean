import Mathlib
import sympy.Basic


/--
[Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType.lean)
-/

private lemma  moduleFinite_and_finiteType
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (A : Type*) [CommRing A] [Algebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Algebra.FiniteType R B] :
    Module.Finite A B ∧ Algebra.FiniteType R A := by

  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G

  have hftAB : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType R A B

  have hfin : Module.Finite A B := Algebra.IsIntegral.finite
  refine ⟨hfin, ?_⟩

  have hAC : (⊤ : Subalgebra R B).FG := Algebra.FiniteType.out
  have hBC : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  exact ⟨fg_of_fg_of_fg R A B hAC hBC hinj⟩
@[main]
private lemma main
  [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [FaithfulSMul A B] [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G] [Algebra.FiniteType R B] :
-- imply
  Module.Finite A B ∧ Algebra.FiniteType R A :=
-- proof
  moduleFinite_and_finiteType R A B G


-- created on 2026-10-05
