import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3
open DivisorsPicard
open scoped nonZeroDivisors


namespace DivisorsPicard

/--
[pic_eq_divC_mod_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma pic_eq_divC_mod_principal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {I : Ideal A}
-- given
  (hI : I ∈ (Ideal A)⁰) :
-- imply
  ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ Submodule.IsPrincipal I :=
-- proof
  ClassGroup.mk0_eq_one_iff hI

end DivisorsPicard

namespace DivisorsPicard

/--
[ufd_dedekind_is_pid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma ufd_dedekind_is_pid
  {R : Type*}
  [CommRing R]
  [IsDedekindDomain R]
  [UniqueFactorizationMonoid R] :
-- imply
  IsPrincipalIdealRing R :=
-- proof
  IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid R

end DivisorsPicard

namespace DivisorsPicard

/--
[classGroup_subsingleton_of_ufd_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma classGroup_subsingleton_of_ufd_dedekind
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [UniqueFactorizationMonoid R] :
-- imply
  Subsingleton (ClassGroup R) := by
-- proof
  haveI : IsPrincipalIdealRing R := ufd_dedekind_is_pid R
  rw [← Fintype.card_le_one_iff_subsingleton]
  exact Nat.le_of_eq card_classGroup_eq_one

end DivisorsPicard

namespace DivisorsPicard

/--
[ufd_prime_contains_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma ufd_prime_contains_prime
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [UniqueFactorizationMonoid R]
  {P : Ideal R}
  [hP : P.IsPrime]
-- given
  (hne : P ≠ ⊥) :
-- imply
  ∃ p ∈ P, Prime p :=
-- proof
  hP.exists_mem_prime_of_ne_bot hne

end DivisorsPicard

namespace DivisorsPicard

/--
[weilCartierFactorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma weilCartierFactorization
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : FractionalIdeal R⁰ K}
-- given
  (hI : I ≠ 0) :
-- imply
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (cartierToWeilDivisor R K I v) = I := by
-- proof
  have key := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hI
  simp only [cartierToWeilDivisor, Finsupp.ofSupportFinite_coe] at key ⊢
  exact key
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] in

end DivisorsPicard

namespace DivisorsPicard

/--
[dvr_is_ufd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma dvr_is_ufd
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R] :
-- imply
  UniqueFactorizationMonoid R :=
-- proof
  inferInstance

end DivisorsPicard

namespace DivisorsPicard

/--
[dvr_is_pid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma dvr_is_pid
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R] :
-- imply
  IsPrincipalIdealRing R :=
-- proof
  inferInstance

end DivisorsPicard

namespace DivisorsPicard

/--
[dedekind_isLocallyFactorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma dedekind_isLocallyFactorial
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R] :
-- imply
  IsLocallyFactorial R := by
-- proof
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    haveI : Ideal.IsPrime (⊥ : Ideal R) := hP
    exact inferInstance
  · haveI := hP
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hbot _
    exact inferInstance

end DivisorsPicard

namespace DivisorsPicard

/--
[ufd_height_one_prime_isPrincipal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma ufd_height_one_prime_isPrincipal
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [UniqueFactorizationMonoid R]
  {P : Ideal R}
  [hP : P.IsPrime]
-- given
  (hne : P ≠ ⊥)
  (hmin : ∀ (Q : Ideal R) [Q.IsPrime], Q ≤ P → Q ≠ ⊥ → Q = P) :
-- imply
  Submodule.IsPrincipal P := by
-- proof
  obtain ⟨p, hpP, hp⟩ := hP.exists_mem_prime_of_ne_bot hne
  have hp0 : p ≠ 0 := hp.ne_zero
  have hspan_prime : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp0).mpr hp
  have hspan_le : Ideal.span {p} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpP)
  have hspan_ne : Ideal.span {p} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [← @hmin (Ideal.span {p}) hspan_prime hspan_le hspan_ne]
  exact ⟨⟨p, rfl⟩⟩

end DivisorsPicard

namespace DivisorsPicard

/--
[ideal_locally_principal_of_locally_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma ideal_locally_principal_of_locally_factorial
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  {I : Ideal R}
  [hI : I.IsPrime]
  {P : Ideal R}
  [hPprime : P.IsPrime]
-- given
  (hlf : IsLocallyFactorial R)
  (hIne : I ≠ ⊥)
  (hht1 : ∀ (Q : Ideal R) [Q.IsPrime], Q ≤ I → Q ≠ ⊥ → Q = I) :
-- imply
  Submodule.IsPrincipal (I.map (algebraMap R (Localization.AtPrime P))) := by
-- proof
  by_cases hle : I ≤ P
  ·
    haveI hUFD : UniqueFactorizationMonoid (Localization.AtPrime P) := hlf P
    have hdisj : Disjoint (P.primeCompl : Set R) (I : Set R) := by
      rw [Set.disjoint_left]; intro x hx hxI; exact hx (hle hxI)
    have hImap_prime : (I.map (algebraMap R (Localization.AtPrime P))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ I hI hdisj
    have hImap_ne : I.map (algebraMap R (Localization.AtPrime P)) ≠ ⊥ := by
      intro h
      have : I = ⊥ := by
        rw [eq_bot_iff]; intro x hx
        have hmap := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime P)) hx
        rw [h] at hmap; simp only [Ideal.mem_bot] at hmap
        exact (IsLocalization.injective (Localization.AtPrime P)
          P.primeCompl_le_nonZeroDivisors) (by rw [hmap, map_zero])
      exact hIne this
    have hImap_min : ∀ (J : Ideal (Localization.AtPrime P)) [J.IsPrime],
      J ≤ I.map (algebraMap R (Localization.AtPrime P)) → J ≠ ⊥ →
      J = I.map (algebraMap R (Localization.AtPrime P)) := by
      intro J hJprime hJle hJne
      have hJcomap_prime : (J.comap (algebraMap R (Localization.AtPrime P))).IsPrime :=
        Ideal.IsPrime.comap (algebraMap R (Localization.AtPrime P))
      have hJcomap_le : J.comap (algebraMap R (Localization.AtPrime P)) ≤ I := by
        calc J.comap (algebraMap R (Localization.AtPrime P))
          ≤ (I.map (algebraMap R (Localization.AtPrime P))).comap
            (algebraMap R (Localization.AtPrime P)) := Ideal.comap_mono hJle
          _ = I := IsLocalization.comap_map_of_isPrime_disjoint P.primeCompl _ hI hdisj
      have hJcomap_ne : J.comap (algebraMap R (Localization.AtPrime P)) ≠ ⊥ := by
        intro h; apply hJne
        have : J = (J.comap (algebraMap R (Localization.AtPrime P))).map
          (algebraMap R (Localization.AtPrime P)) :=
          (IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) J).symm
        rw [this, h, Ideal.map_bot]
      have heq := @hht1 _ hJcomap_prime hJcomap_le hJcomap_ne
      calc J = (J.comap (algebraMap R (Localization.AtPrime P))).map
        (algebraMap R (Localization.AtPrime P)) :=
        (IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) J).symm
        _ = I.map (algebraMap R (Localization.AtPrime P)) := by rw [heq]
    exact @ufd_height_one_prime_isPrincipal _ _ hUFD _ hImap_prime hImap_ne hImap_min
  ·
    have : I.map (algebraMap R (Localization.AtPrime P)) = ⊤ :=
      IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hle
    rw [this]
    exact ⟨⟨1, by simp⟩⟩

end DivisorsPicard

namespace DivisorsPicard

/--
[ideal_locally_principal_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma ideal_locally_principal_dedekind
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {I : Ideal R}
  {P : Ideal R}
  [P.IsPrime]
-- given
  (hP : P ≠ ⊥) :
-- imply
  Submodule.IsPrincipal (I.map (algebraMap R (Localization.AtPrime P))) := by
-- proof
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    dedekind_localization_dvr R P hP
  haveI : IsPrincipalIdealRing (Localization.AtPrime P) := inferInstance
  exact IsPrincipalIdealRing.principal _

end DivisorsPicard

namespace DivisorsPicard

/--
[classGroup_measures_weil_cartier_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma classGroup_measures_weil_cartier_obstruction
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {I : Ideal R}
-- given
  (hI : I ∈ (Ideal R)⁰) :
-- imply
  ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ Submodule.IsPrincipal I :=
-- proof
  ClassGroup.mk0_eq_one_iff hI

end DivisorsPicard

namespace DivisorsPicard

/--
[pic_affine_line_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma pic_affine_line_trivial
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {k : Type*}
  [Field k] :
-- imply
  Fintype.card (ClassGroup (Polynomial k)) = 1 :=
-- proof
  card_classGroup_eq_one

end DivisorsPicard

namespace DivisorsPicard

/--
[power_series_ufd_of_pid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma power_series_ufd_of_pid
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsPrincipalIdealRing R] :
-- imply
  UniqueFactorizationMonoid (PowerSeries R) :=
-- proof
  inferInstance

end DivisorsPicard

namespace DivisorsPicard

/--
[classNumber_one_of_pid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma classNumber_one_of_pid
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsPrincipalIdealRing R] :
-- imply
  Fintype.card (ClassGroup R) = 1 :=
-- proof
  card_classGroup_eq_one

end DivisorsPicard

namespace DivisorsPicard

/--
[classGroup_trivial_iff_pid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma classGroup_trivial_iff_pid
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [Fintype (ClassGroup R)] :
-- imply
  Fintype.card (ClassGroup R) = 1 ↔ IsPrincipalIdealRing R :=
-- proof
  card_classGroup_eq_one_iff

end DivisorsPicard

namespace DivisorsPicard

/--
[fg_torsionfree_free_of_pid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma fg_torsionfree_free_of_pid
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsPrincipalIdealRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [NoZeroSMulDivisors R M] :
-- imply
  Module.Free R M := by
-- proof
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  exact Module.Free.of_basis (Module.basisOfFiniteTypeTorsionFree hs).2

end DivisorsPicard

namespace DivisorsPicard

/--
[mem_principalCartierDivisors_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean)
-/
@[path]
lemma mem_principalCartierDivisors_iff
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {D : (FractionalIdeal A⁰ K)ˣ} :
-- imply
  D ∈ PrincipalCartierDivisors A K ↔ ∃ x : K, FractionalIdeal.spanSingleton A⁰ x = (D : FractionalIdeal A⁰ K) :=
-- proof
  mem_principal_ideals_iff

end DivisorsPicard


-- created on 2026-10-23
