import Mathlib
import sympy.Basic
import Def.RingTheory.DedekindDomain.ElementDifferent


/--
[elementDifferent_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
lemma elementDifferent_of_adjoin_eq_top
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L]
  {α : B}
-- given
  (hα : Algebra.adjoin K {algebraMap B L α} = ⊤) :
-- imply
  elementDifferent A K L α =
    Polynomial.aeval α (Polynomial.derivative (minpoly A α)) := by
-- proof
  classical
  unfold elementDifferent
  rw [ite_eq_left hα]

/--
[elementDifferent_of_adjoin_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
lemma elementDifferent_of_adjoin_ne_top
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L]
  {α : B}
-- given
  (hα : Algebra.adjoin K {algebraMap B L α} ≠ ⊤) :
-- imply
  elementDifferent A K L α = 0 := by
-- proof
  classical
  unfold elementDifferent
  rw [ite_eq_right hα]

/--
[elementDifferent_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
lemma elementDifferent_eq_zero_iff
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L]
  {α : B} :
-- imply
  elementDifferent A K L α = 0 ↔
    Algebra.adjoin K {algebraMap B L α} ≠ ⊤ ∨
    Polynomial.aeval α (Polynomial.derivative (minpoly A α)) = 0 := by
-- proof
  classical
  unfold elementDifferent
  split_ifs with h
  · simp [h]
  · simp [h]

/--
[elementDifferent_mem_differentIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
lemma elementDifferent_mem_differentIdeal
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L] [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  {α : B}
-- given
  (hα : Algebra.adjoin K {algebraMap B L α} = ⊤) :
-- imply
  elementDifferent A K L α ∈ differentIdeal A B := by
-- proof
  rw [elementDifferent_of_adjoin_eq_top A K L α hα]
  exact aeval_derivative_mem_differentIdeal A K L α hα

/--
[differentIdeal_eq_span_derivative_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/ElementDifferent.lean)
-/
@[path]
lemma differentIdeal_eq_span_derivative_of_adjoin_eq_top
  [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A B] [Algebra B L] [Algebra K L] [Algebra A K] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsFractionRing B L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  {α : B}
-- given
  (hα : Algebra.adjoin A {α} = ⊤) :
-- imply
  differentIdeal A B =
    Ideal.span {Polynomial.aeval α (Polynomial.derivative (minpoly A α))} := by
-- proof
  have hmemB : ∀ b : B,
    algebraMap B L b ∈ IntermediateField.adjoin K {algebraMap B L α} := by
    intro b
    have hb : b ∈ Algebra.adjoin A {α} := by
      rw [hα]
      exact Set.mem_univ b
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb
    · intro x hx
      have hxα : x = α := Set.mem_singleton_iff.mp hx
      subst hxα
      apply IntermediateField.subset_adjoin
      rfl
    · intro r
      have heq : algebraMap B L (algebraMap A B r) =
        algebraMap K L (algebraMap A K r) := by
        calc
          algebraMap B L (algebraMap A B r) = algebraMap A L r :=
            (IsScalarTower.algebraMap_apply A B L r).symm
          _ = algebraMap K L (algebraMap A K r) :=
            IsScalarTower.algebraMap_apply A K L r
      rw [heq]
      exact (IntermediateField.adjoin K {algebraMap B L α}).algebraMap_mem _
    · intro x y _ _ hx hy
      simpa only [map_add] using add_mem hx hy
    · intro x y _ _ hx hy
      simpa only [map_mul] using mul_mem hx hy
  have hIF : IntermediateField.adjoin K {algebraMap B L α} = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective B y
    exact div_mem (hmemB a) (hmemB b)
  have hfield : Algebra.adjoin K {algebraMap B L α} = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff).mp hIF
  have hmul := conductor_mul_differentIdeal A K L α hfield
  rwa [conductor_eq_top_of_adjoin_eq_top hα, Ideal.top_mul] at hmul


-- created on 2026-10-20
-- updated on 2026-10-23
