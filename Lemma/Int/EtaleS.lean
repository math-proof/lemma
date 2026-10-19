import Lemma.Int.FormallyEtale.of.Bijective
import Mathlib
open Int KaehlerDifferential


private lemma mapBaseChange_surjective_of_formallyUnramified
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyUnramified S T] :
-- imply
  Function.Surjective (KaehlerDifferential.mapBaseChange R S T) := by
-- proof
  intro y
  apply (KaehlerDifferential.exact_mapBaseChange_map R S T y).mp (Subsingleton.elim _ _)


private lemma bijective_of_surjective_of_finrank_eq
  [CommRing A] [Nontrivial A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]
  (f : M →ₗ[A] N)
-- given
  (hf : Function.Surjective f)
  (hrank : Module.finrank A M = Module.finrank A N) :
-- imply
  Function.Bijective f := by
-- proof
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hrank
  apply OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap f e.injective hf


/--
[Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (n : ℕ)
  [Algebra.IsStandardSmoothOfRelativeDimension n R S]
  [Algebra.IsStandardSmoothOfRelativeDimension n R T]
  [Algebra.FormallyUnramified S T] :
-- imply
  Algebra.Etale S T := by
-- proof
  have : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.IsStandardSmooth R T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have : Algebra.FormallyEtale S T := by
    refine FormallyEtale.of.Bijective (R := R) ?_
    have hsurj := mapBaseChange_surjective_of_formallyUnramified (R := R) (S := S) (T := T)
    obtain hT | hT := subsingleton_or_nontrivial T
    ·
      refine ⟨fun a b _ => Subsingleton.elim _ _, hsurj⟩
    ·
      have : Nontrivial S := (algebraMap S T).domain_nontrivial
      have hS : Module.rank S Ω[S⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hTr : Module.rank T Ω[T⁄R] = n :=
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
      have hSf : Module.finrank S Ω[S⁄R] = n := Module.finrank_eq_of_rank_eq hS
      have hTf : Module.finrank T Ω[T⁄R] = n := Module.finrank_eq_of_rank_eq hTr
      apply bijective_of_surjective_of_finrank_eq _ hsurj
      rw [Module.finrank_baseChange, hSf, hTf]
  have : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  refine ⟨(inferInstance : Algebra.FormallyEtale S T), (inferInstance : Algebra.FinitePresentation S T)⟩


-- created on 2026-10-13
