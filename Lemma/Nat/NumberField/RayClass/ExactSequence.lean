import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.NumberField.RayClass.RayClassToClassGroup.Part2
import Lemma.Nat.NumberField.RayClass.RayClassToClassGroup
open scoped nonZeroDivisors
open NumberField


namespace NumberField.Modulus

/--
[fractionalIdealMk0_mem_coprimeFractionalIdeals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
lemma fractionalIdealMk0_mem_coprimeFractionalIdeals
  [Field K] [NumberField K]
  {m : Modulus K}
  {I : nonZeroDivisors (Ideal (𝓞 K))}
-- given
  (hI : IsCoprime (I : Ideal (𝓞 K)) (m.finitePart : Ideal (𝓞 K))) :
-- imply
  FractionalIdeal.mk0 K I ∈ coprimeFractionalIdeals m := by
-- proof
  rw [mem_coprimeFractionalIdeals_iff]
  intro v hv
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hsup := hI.sup_eq
  have hv' : (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal := hv
  have hndvd : ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    intro hdvd
    have hle : (I : Ideal (𝓞 K)) ⊔ (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal :=
      sup_le (Ideal.dvd_iff_le.mp hdvd) hv'
    rw [hsup] at hle
    exact v.isPrime.ne_top (top_le_iff.mp hle)
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe K v hI0]
  have hcount : (Associates.mk v.asIdeal).count
    (Associates.mk (I : Ideal (𝓞 K))).factors = 0 := by
    by_contra hne
    exact hndvd
      ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne)
  exact Nat.cast_eq_zero.mpr hcount

end NumberField.Modulus


namespace NumberField.Modulus

/-- A class-group class has a nonzero integral representative coprime to a given
nonzero ideal. -/
lemma exists_mk0_eq_and_isCoprime
  [Field K] [NumberField K]
  {A : Ideal (𝓞 K)}
-- given
  (c : ClassGroup (𝓞 K))
  (hA : A ≠ 0) :
-- imply
  ∃ J : (Ideal (𝓞 K))⁰, ClassGroup.mk0 J = c ∧ IsCoprime (J : Ideal (𝓞 K)) A := by
-- proof
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  by_cases htop : A = ⊤
  ·
    refine ⟨I, rfl, ?_⟩
    rw [htop, Ideal.isCoprime_iff_sup_eq, sup_top_eq]
  ·
    have hI : (I : Ideal (𝓞 K)) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp I.property
    have hA0 : (A : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa using hA)
    have hI0 : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa using hI)
    obtain ⟨x, hx⟩ :=
      IsDedekindDomain.exists_add_spanSingleton_mul_eq
        (a := (A : FractionalIdeal (𝓞 K)⁰ K))
        (b := ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
        (c := (1 : FractionalIdeal (𝓞 K)⁰ K))
        FractionalIdeal.coeIdeal_le_one hA0 hI0
    set Jfrac := FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
      ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    have hsum : (A : FractionalIdeal (𝓞 K)⁰ K) + Jfrac = 1 := by
      simpa [Jfrac] using hx
    have hle : Jfrac ≤ 1 :=
      (le_add_self (a := Jfrac) (b := (A : FractionalIdeal (𝓞 K)⁰ K))).trans
        (le_of_eq hsum)
    obtain ⟨Jideal, hJeq⟩ := (FractionalIdeal.le_one_iff_exists_coeIdeal).mp hle
    have hx0 : x ≠ 0 := by
      intro hx0
      have hA1 : (A : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
        simpa [hx0, Jfrac, add_zero] using hx
      exact htop ((FractionalIdeal.coeIdeal_eq_one.mp hA1).trans Ideal.one_eq_top)
    have hJne : Jideal ≠ 0 := by
      intro h0
      have hJ0 : Jfrac = 0 := by simpa [h0] using hJeq.symm
      have hspan0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = 0 := by
        have : FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
            ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
          simpa [Jfrac] using hJ0
        exact (mul_eq_zero.mp this).resolve_right hI0
      exact hx0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hspan0)
    let J : (Ideal (𝓞 K))⁰ :=
      ⟨Jideal, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa using hJne)⟩
    refine ⟨J, ?_, ?_⟩
    ·
      refine (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (K := K)).mpr ?_
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
      have hJeq' : (Jideal : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
            ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        simpa [Jfrac] using hJeq
      have : FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
          (Jideal : FractionalIdeal (𝓞 K)⁰ K) =
          ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        calc
          FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
              (Jideal : FractionalIdeal (𝓞 K)⁰ K)
              = FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
                (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
                  ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) := by
            rw [hJeq']
          _ = (FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
                FractionalIdeal.spanSingleton (𝓞 K)⁰ x) *
              ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [← mul_assoc]
          _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (x⁻¹ * x) *
              ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [← map_mul]
          _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ 1 *
              ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [inv_mul_cancel₀ hx0]
          _ = (1 : FractionalIdeal (𝓞 K)⁰ K) *
              ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [map_one]
          _ = ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [one_mul]
      change FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹ *
          (Jideal : FractionalIdeal (𝓞 K)⁰ K) =
          ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      exact this
    ·
      rw [Ideal.isCoprime_iff_sup_eq]
      have : ((Jideal ⊔ A : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
        rw [FractionalIdeal.coeIdeal_sup, hJeq, add_comm, hsum]
      exact (FractionalIdeal.coeIdeal_eq_one.mp this).trans Ideal.one_eq_top

end NumberField.Modulus

namespace NumberField.Modulus

/--
[coprimeIdealClassMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
lemma coprimeIdealClassMap_surjective
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Surjective (coprimeIdealClassMap m) := by
-- proof
  intro c
  obtain ⟨I, hJclass, hJcop⟩ :=
    exists_mk0_eq_and_isCoprime c
      (mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property)
  have hmem := fractionalIdealMk0_mem_coprimeFractionalIdeals hJcop
  refine ⟨⟨FractionalIdeal.mk0 K I, hmem⟩, ?_⟩
  have hsub : (coprimeFractionalIdeals m).subtype
    (⟨FractionalIdeal.mk0 K I, hmem⟩ : coprimeFractionalIdeals m) =
    FractionalIdeal.mk0 K I := rfl
  simpa [coprimeIdealClassMap_apply, hsub, ClassGroup.mk_mk0] using hJclass

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayClassToClassGroup_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
lemma rayClassToClassGroup_surjective
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Surjective (rayClassToClassGroup m) := by
-- proof
  intro c
  obtain ⟨I, hI⟩ := coprimeIdealClassMap_surjective c
  exact ⟨rayClassMap m I, (rayClassToClassGroup_rayClassMap m I).trans hI⟩

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayClass_six_term_exact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
lemma rayClass_six_term_exact
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralRayOneUnitsInclusion m) ∧
    Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToRayQuotient m) ∧
    Function.MulExact (integralUnitsToRayQuotient m)
    (rayQuotientToRayClassGroup m) ∧
    Function.MulExact (rayQuotientToRayClassGroup m)
    (rayClassToClassGroup m) ∧
    Function.Surjective (rayClassToClassGroup m) :=
-- proof
  ⟨integralRayOneUnitsInclusion_injective,
    integralUnits_mulExact_quotient,
    integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup,
    rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup,
    rayClassToClassGroup_surjective⟩

end NumberField.Modulus

namespace NumberField.Modulus

/--
[rayClass_residueSign_six_term_exact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ExactSequence.lean)
-/
@[path]
lemma rayClass_residueSign_six_term_exact
  [Field K] [NumberField K]
  {m : Modulus K} :
-- imply
  Function.Injective (integralRayOneUnitsInclusion m) ∧
    Function.MulExact (integralRayOneUnitsInclusion m)
    (integralUnitsToResidueSign m) ∧
    Function.MulExact (integralUnitsToResidueSign m)
    (residueSignToRayClassGroup m) ∧
    Function.MulExact (residueSignToRayClassGroup m)
    (rayClassToClassGroup m) ∧
    Function.Surjective (rayClassToClassGroup m) :=
-- proof
  ⟨integralRayOneUnitsInclusion_injective,
    integralUnits_mulExact_residueSign,
    integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup,
    residueSignToRayClassGroup_mulExact_rayClassToClassGroup,
    rayClassToClassGroup_surjective⟩

end NumberField.Modulus


-- created on 2026-10-20
-- updated on 2026-11-13
