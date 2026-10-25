/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DiscreteValuationRing/Monogenic.lean -/

/-
Author: Muse Code
-/

import Mathlib.RingTheory.PowerSeries.Inverse
import Theorem.RingTheory.DiscreteValuationRing.Monogenic
import Lemma.Int.DiscreteValuationRing.Monogenic
open IsLocalRing IsDiscreteValuationRing
open scoped PowerSeries

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]

/-!
# Tests for monogenicity of finite DVR extensions

These examples exercise the three public theorems of
`MathlibExt.RingTheory.DiscreteValuationRing.Monogenic`: the ramified monogenicity
theorem, the unramified refinement, and the strengthened structured-witness theorem
returning the generator together with a monic lift of the residue minimal polynomial
whose value generates the maximal ideal, including the composition of the refinement
with the primitive element theorem and an end-to-end check on the identity extension.
-/


/-- The ramified monogenicity theorem applies as stated. -/
example [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ :=
  exists_adjoin_eq_top_of_separable_residueField

/-- The unramified refinement composed with a lifted primitive element yields a
generator. -/
example [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (hunram : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ∃ β : B, Algebra.adjoin A ({β} : Set B) = ⊤ := by
  obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField B)
  obtain ⟨β, hβ⟩ := residue_surjective (R := B) α₀
  have hadj : Algebra.adjoin (ResidueField A) ({α₀} : Set _) = ⊤ := by
    have h := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite _ _ : IsAlgebraic (ResidueField A) α₀)
    rw [hα₀, IntermediateField.top_toSubalgebra] at h
    exact h.symm
  refine ⟨β, adjoin_eq_top_of_lift_of_map_maximalIdeal hunram ?_⟩
  rw [hβ]
  exact hadj

/-- End-to-end check on the identity extension: the main theorem fires with the
identity algebra (the residue extension is trivially separable). -/
example (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ∃ α : A, Algebra.adjoin A ({α} : Set A) = ⊤ := by
  let _ : Algebra A A := Algebra.id A
  exact exists_adjoin_eq_top_of_separable_residueField

/-- Generic application of the étale criterion. -/
example [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (hfin : Module.finrank A B = Module.finrank (ResidueField A) (ResidueField B)) :
    Algebra.Etale A B :=
  etale_of_isSeparable_residueField_of_finrank_eq hfin

/-- Identity extension is étale via the finrank criterion. -/
example (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    Algebra.Etale A A := by
  let _ : Algebra A A := Algebra.id A
  have hfin := IsLocalRing.finrank_eq_finrank_residueField (R := A) (S := A)
  exact etale_of_isSeparable_residueField_of_finrank_eq hfin

/-- Generic downstream use of the strengthened theorem: every returned field
is consumed. `F` is generally not `minpoly A α`: `aeval α F` is a nonzero
uniformizer while `aeval α (minpoly A α) = 0`. -/
example [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ (α : B) (F : Polynomial A),
      Algebra.adjoin A ({α} : Set B) = ⊤ ∧ F.Monic ∧
        Polynomial.aeval α F ∈ maximalIdeal B ∧
        Polynomial.aeval α F ≠ 0 ∧ F ≠ minpoly A α ∧
        IsUnit (Polynomial.aeval α F.derivative) ∧
        maximalIdeal B = Ideal.span {Polynomial.aeval α F} ∧
        Algebra.adjoin (ResidueField A) ({residue B α} : Set _) = ⊤ ∧
        F.map (residue A) = minpoly (ResidueField A) (residue B α) := by
  obtain ⟨α, F, hgen, hresgen, hmonic, hFmap, hderiv, hspan⟩ :=
    exists_generator_with_residue_minpoly_uniformizer (A := A) (B := B)
  have hmem : Polynomial.aeval α F ∈ maximalIdeal B := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self _
  have hne : Polynomial.aeval α F ≠ 0 := by
    intro h0
    have hbot : maximalIdeal B = ⊥ := by
      rw [hspan, h0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    exact not_a_field (R := B) hbot
  have hFne : F ≠ minpoly A α := by
    intro hEq
    apply hne
    rw [hEq]
    exact minpoly.aeval A α
  refine ⟨α, F, hgen, hmonic, hmem, hne, hFne, hderiv, hspan, hresgen, hFmap⟩

/-- Closed specialization over `ℚ⟦X⟧`: the identity extension yields a monic
polynomial whose value is a uniformizer with unit derivative value. -/
example : ∃ (α : ℚ⟦X⟧) (F : Polynomial ℚ⟦X⟧),
    F.Monic ∧ Polynomial.aeval α F ≠ 0 ∧
      IsUnit (Polynomial.aeval α F.derivative) ∧
      maximalIdeal ℚ⟦X⟧ = Ideal.span {Polynomial.aeval α F} := by
  let _ : Algebra ℚ⟦X⟧ ℚ⟦X⟧ := Algebra.id _
  obtain ⟨α, F, -, -, hmonic, -, hderiv, hspan⟩ :=
    exists_generator_with_residue_minpoly_uniformizer
      (A := ℚ⟦X⟧) (B := ℚ⟦X⟧)
  have hne : Polynomial.aeval α F ≠ 0 := by
    intro h0
    have hbot : maximalIdeal ℚ⟦X⟧ = ⊥ := by
      rw [hspan, h0]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    exact not_a_field (R := ℚ⟦X⟧) hbot
  exact ⟨α, F, hmonic, hne, hderiv, hspan⟩

