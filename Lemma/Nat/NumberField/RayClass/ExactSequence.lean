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
  obtain ⟨J, hJne, hJclass, hJcop⟩ :=
    ClassGroup.exists_mk0_eq_and_isCoprime c
      (m.finitePart : Ideal (𝓞 K))
      (mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property)
  have hJne0 : J ≠ 0 := by simpa using hJne
  let I : nonZeroDivisors (Ideal (𝓞 K)) :=
    ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJne0⟩
  have hJcop' : IsCoprime (I : Ideal (𝓞 K))
    (m.finitePart : Ideal (𝓞 K)) := hJcop
  have hmem := fractionalIdealMk0_mem_coprimeFractionalIdeals m I hJcop'
  refine ⟨⟨FractionalIdeal.mk0 K I, hmem⟩, ?_⟩
  have hsub : (coprimeFractionalIdeals m).subtype
    (⟨FractionalIdeal.mk0 K I, hmem⟩ : coprimeFractionalIdeals m) =
    FractionalIdeal.mk0 K I := rfl
  rwa [coprimeIdealClassMap_apply, hsub, ClassGroup.mk_mk0]

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
  obtain ⟨I, hI⟩ := coprimeIdealClassMap_surjective m c
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
  ⟨integralRayOneUnitsInclusion_injective m,
    integralUnits_mulExact_quotient m,
    integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup m,
    rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup m,
    rayClassToClassGroup_surjective m⟩

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
  ⟨integralRayOneUnitsInclusion_injective m,
    integralUnits_mulExact_residueSign m,
    integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup m,
    residueSignToRayClassGroup_mulExact_rayClassToClassGroup m,
    rayClassToClassGroup_surjective m⟩

end NumberField.Modulus


-- created on 2026-10-20
-- updated on 2026-10-26
