import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma nontrivial_quotient_of_ne_top
  {A : Type} [CommRing A]
  {I : Ideal A}
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  Nontrivial (A ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr hI

private lemma isLocalRing_quotient_of_ne_top
  {A : Type} [CommRing A] [IsLocalRing A]
  {I : Ideal A}
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  IsLocalRing (A ⧸ I) :=
  let _ := nontrivial_quotient_of_ne_top hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private lemma isLocalHom_mk_of_ne_top
  {A : Type} [CommRing A] [IsLocalRing A]
  {I : Ideal A}
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  IsLocalHom (Ideal.Quotient.mk I) :=
  let _ := nontrivial_quotient_of_ne_top hI
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

private lemma map_maximalIdeal_mk_of_ne_top
  {A : Type} [CommRing A] [IsLocalRing A]
  {I : Ideal A} [IsLocalRing (A ⧸ I)]
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
  -- proof
  let _ := isLocalHom_mk_of_ne_top hI
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (le_maximalIdeal hI), mem_maximalIdeal,
    mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

/--
[IsLocalRing_ResidueField_algebraMap_surjective_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_ResidueField_algebraMap_surjective_quotient.lean)
-/
@[path]
private lemma main
  {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
  (I : Ideal A) [IsLocalRing (A ⧸ I)]
  -- given
  (h : Function.Surjective (algebraMap 𝒪 (ResidueField A))) :
  -- imply
  Function.Surjective (algebraMap 𝒪 (ResidueField (A ⧸ I))) := by
  -- proof
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨o, ho⟩ := h (residue A a)
  refine ⟨o, ?_⟩
  change residue (A ⧸ I) (Ideal.Quotient.mk I (algebraMap 𝒪 A o)) =
    residue (A ⧸ I) (Ideal.Quotient.mk I a)
  change residue A (algebraMap 𝒪 A o) = residue A a at ho
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at ho ⊢
  rw [← map_sub, ← map_maximalIdeal_mk_of_ne_top hI]
  apply Ideal.mem_map_of_mem _ ho


-- created on 2026-10-20
