import Mathlib
import Lemma.Definitions.Def_Deformations_ProartinianCat

set_option autoImplicit false

universe u

open CategoryTheory Function IsLocalRing Filter Topology Set Pointwise

private lemma IsArtinianRing.finite_of_finite_residueField (R : Type*) [CommRing R] [IsArtinianRing R]
    [IsLocalRing R] [Empty.Finite (ResidueField R)] : Empty.Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  have h1 : Empty.Finite (R ⧸ maximalIdeal R) := ‹Empty.Finite (ResidueField R)›
  have h2 : Empty.Finite (R ⧸ maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  rw [hn, Ideal.zero_eq_bot] at h2
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

namespace IsProartinian

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [IsLocalRing R] [IsProartinian R] [Empty.Finite (ResidueField R)]

private lemma finite_quotient_of_isOpen (I : Ideal R) (hI : IsOpen (X := R) I) :
    Empty.Finite (R ⧸ I) := by
  by_cases hI' : I = ⊤
  · have : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI'
    exact Empty.Finite.of_subsingleton

  have := IsProartinian.isArtinianRing_quotient I hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI'
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective

  have hsurj : Function.Surjective (ResidueField.map (Ideal.Quotient.mk I)) := by
    have hcomp : Function.Surjective
        (ResidueField.map (Ideal.Quotient.mk I) ∘ residue R) := by
      rw [show ResidueField.map (Ideal.Quotient.mk I) ∘ residue R
            = residue (R ⧸ I) ∘ Ideal.Quotient.mk I from
          funext fun r ↦ ResidueField.map_residue _ r]
      exact (residue_surjective).comp Ideal.Quotient.mk_surjective
    exact hcomp.of_comp
  have : Empty.Finite (ResidueField (R ⧸ I)) := .of_surjective _ hsurj
  exact IsArtinianRing.finite_of_finite_residueField (R ⧸ I)

private lemma compactSpace_of_finite_residueField : CompactSpace R := by
  letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  haveI : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, completeSpace_iff_isComplete_univ.mp inferInstance⟩
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU

  obtain ⟨I, hI_open, hI_sub⟩ := (IsLinearTopology.hasBasis_open_ideal (R := R)).mem_iff.mp hU

  have : Empty.Finite (R ⧸ I) := finite_quotient_of_isOpen I hI_open
  obtain ⟨sec, hsec⟩ := (Ideal.Quotient.mk_surjective (I := I)).hasRightInverse
  refine ⟨Set.range sec, Set.finite_range sec, fun x _ ↦ ?_⟩

  refine Set.mem_iUnion₂.mpr ⟨sec (Ideal.Quotient.mk I x), ⟨_, rfl⟩, ?_⟩
  refine Set.mem_vadd_set.mpr ⟨x - sec (Ideal.Quotient.mk I x), hI_sub ?_, ?_⟩
  · show x - sec (Ideal.Quotient.mk I x) ∈ I
    rw [← Ideal.Quotient.eq]
    exact (hsec _).symm
  · show sec (Ideal.Quotient.mk I x) + (x - sec (Ideal.Quotient.mk I x)) = x
    abel

end IsProartinian

namespace Deformation.ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

instance instFiniteResidueField [Empty.Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    Empty.Finite (ResidueField A) :=
  .of_surjective _ (IsResidueAlgebra.algebraMap_bijective 𝓞 A).surjective

instance instCompactSpace [Empty.Finite (ResidueField 𝓞)] (A : ProartinianCat 𝓞) :
    CompactSpace A :=
  IsProartinian.compactSpace_of_finite_residueField

end Deformation.ProartinianCat
