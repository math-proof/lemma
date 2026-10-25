/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/LocalRing/ResidueField/AdjoinRootLift.lean -/


import Def.RingTheory.LocalRing.ResidueField.AdjoinRootLift.Part3
import Lemma.Int.LocalRing.ResidueField.AdjoinRootLift
open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]


/-- `X` over the residue field lifts to a monic with domain `AdjoinRoot`. -/
example : ∃ (g : A[X]) (_ : g.Monic) (_ : IsDomain (AdjoinRoot g))
    (_ : Module.Finite A (AdjoinRoot g)),
    g.map (IsLocalRing.residue A) = X := by
  obtain ⟨g, hg, hdom, hfin, hmap⟩ :=
    DVRResidue.exists_monic_lift_adjoinRoot_domain (A := A) X monic_X
      irreducible_X
  exact ⟨g, hg, hdom, hfin, hmap⟩

/-- `X - C 1` over the residue field lifts in the same way. -/
example : ∃ (g : A[X]) (_ : g.Monic) (_ : IsDomain (AdjoinRoot g))
    (_ : Module.Finite A (AdjoinRoot g)),
    g.map (IsLocalRing.residue A) = X - C 1 := by
  obtain ⟨g, hg, hdom, hfin, hmap⟩ :=
    DVRResidue.exists_monic_lift_adjoinRoot_domain (A := A) _ (monic_X_sub_C 1)
      (irreducible_X_sub_C 1)
  exact ⟨g, hg, hdom, hfin, hmap⟩

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The quotient equivalence sends the adjoined root to `AdjoinRoot.root gbar`. -/
example (g : R[X]) (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar) :
    DVRResidue.adjoinRootQuotientEquivOfMapEq g gbar hmap
        (Ideal.Quotient.mk _ (AdjoinRoot.mk g X)) =
      AdjoinRoot.root gbar := by
  rw [DVRResidue.adjoinRootQuotientEquivOfMapEq_mk, Polynomial.map_X]
  rfl

/-- The quotient equivalence sends constants to residue coefficients. -/
example (g : R[X]) (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar) (a : R) :
    DVRResidue.adjoinRootQuotientEquivOfMapEq g gbar hmap
        (Ideal.Quotient.mk _ (AdjoinRoot.mk g (C a))) =
      AdjoinRoot.mk gbar (C (IsLocalRing.residue R a)) := by
  rw [DVRResidue.adjoinRootQuotientEquivOfMapEq_mk, Polynomial.map_C]

section LocalLayer

variable (g : R[X]) (hg : g.Monic)
  (hirr : Irreducible (g.map (IsLocalRing.residue R)))

/-- Install the new local-ring witness and check the maximal ideal equality. -/
example :
    let _ : IsLocalRing (AdjoinRoot g) :=
      DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
        (g := g) hg hirr
    IsLocalRing.maximalIdeal (AdjoinRoot g) =
      Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal R) := by
  let _ : IsLocalRing (AdjoinRoot g) :=
    DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := g) hg hirr
  exact DVRResidue.maximalIdeal_adjoinRoot_eq_map (g := g) hirr

/-- The residue-field equivalence sends the adjoined root to `AdjoinRoot.root gbar`. -/
example (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar) :
    let _ : IsLocalRing (AdjoinRoot g) :=
      DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
        (g := g) hg hirr
    DVRResidue.residueFieldEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap
        (IsLocalRing.residue (AdjoinRoot g) (AdjoinRoot.mk g X)) =
      AdjoinRoot.root gbar := by
  dsimp only
  let _ : IsLocalRing (AdjoinRoot g) :=
    DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := g) hg hirr
  rw [DVRResidue.residueFieldEquivAdjoinRootOfMapEq_residue_mk,
    Polynomial.map_X]
  rfl

/-- Constants map to residue coefficients under the residue-field equivalence. -/
example (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar) (a : R) :
    let _ : IsLocalRing (AdjoinRoot g) :=
      DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
        (g := g) hg hirr
    DVRResidue.residueFieldEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap
        (IsLocalRing.residue (AdjoinRoot g) (AdjoinRoot.mk g (C a))) =
      AdjoinRoot.mk gbar (C (IsLocalRing.residue R a)) := by
  dsimp only
  let _ : IsLocalRing (AdjoinRoot g) :=
    DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := g) hg hirr
  rw [DVRResidue.residueFieldEquivAdjoinRootOfMapEq_residue_mk,
    Polynomial.map_C]

end LocalLayer

section DVRStructure

variable (g : A[X]) (hg : g.Monic)
  (hirr : Irreducible (g.map (IsLocalRing.residue A)))
  [IsDomain (AdjoinRoot g)]

/-- Installing D1's domain witness and D3's local witness yields D4. -/
example :
    let _ : IsLocalRing (AdjoinRoot g) :=
      DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
        (g := g) hg hirr
    IsDiscreteValuationRing (AdjoinRoot g) := by
  let _ : IsLocalRing (AdjoinRoot g) :=
    DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := g) hg hirr
  exact DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map
    (g := g) hg hirr

/-- Pipeline from `X`: lift, install domain and locality, obtain DVR. -/
example : ∃ (h : A[X]) (_ : h.Monic) (_ : IsDomain (AdjoinRoot h)),
    IsDiscreteValuationRing (AdjoinRoot h) := by
  obtain ⟨h, hmonic, hdom, _hfin, hmap⟩ :=
    DVRResidue.exists_monic_lift_adjoinRoot_domain (A := A) X monic_X
      irreducible_X
  have hirr : Irreducible (h.map (IsLocalRing.residue A)) :=
    hmap ▸ irreducible_X
  let _ : IsLocalRing (AdjoinRoot h) :=
    DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := h) hmonic hirr
  exact ⟨h, hmonic, hdom,
    DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map
      (g := h) hmonic hirr⟩

/-- After installing D4, the upstairs maximal ideal is principal and nonzero. -/
example [IsLocalRing (AdjoinRoot g)] :
    (IsLocalRing.maximalIdeal (AdjoinRoot g)).IsPrincipal ∧
      IsLocalRing.maximalIdeal (AdjoinRoot g) ≠ ⊥ := by
  let _ : IsDiscreteValuationRing (AdjoinRoot g) :=
    DVRResidue.adjoinRoot_isDiscreteValuationRing_of_monic_of_irreducible_map
      (g := g) hg hirr
  exact ⟨inferInstance, IsDiscreteValuationRing.not_a_field _⟩

end DVRStructure

section EssentialSurjectivity

universe u

/-- Identity residue extension lifts with an AlgEquiv sending 1 to 1. -/
example {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
    (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
    (_ : IsLocalHom (algebraMap A B))
    (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
      (IsLocalRing.ResidueField A)),
    e 1 = 1 := by
  obtain ⟨B, hComm, hDom, hAlg, hFin, hDVR, hLoc, ⟨e⟩⟩ :=
    DVRResidue.exists_finite_dvr_extension_residueField_algEquiv
      (A := A) (IsLocalRing.ResidueField A)
  exact ⟨B, hComm, hDom, hAlg, hFin, hDVR, hLoc, e, map_one e⟩

/-- Any finite separable residue extension lifts with a bijective AlgEquiv. -/
example {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type*) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [FiniteDimensional (IsLocalRing.ResidueField A) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) L] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B)
      (_ : Module.Finite A B) (_ : IsDiscreteValuationRing B)
      (_ : IsLocalHom (algebraMap A B))
      (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] L),
      Function.Bijective e := by
  obtain ⟨B, hComm, hDom, hAlg, hFin, hDVR, hLoc, ⟨e⟩⟩ :=
    DVRResidue.exists_finite_dvr_extension_residueField_algEquiv (A := A) L
  exact ⟨B, hComm, hDom, hAlg, hFin, hDVR, hLoc, e, e.bijective⟩

end EssentialSurjectivity

section AlgEquivCompat

variable (g : R[X]) (hg : g.Monic)
  (hirr : Irreducible (g.map (IsLocalRing.residue R)))

/-- The residue algebra equivalence commutes with base scalars. -/
example (gbar : (IsLocalRing.ResidueField R)[X])
    (hmap : g.map (IsLocalRing.residue R) = gbar)
    (x : IsLocalRing.ResidueField R) :
    let _ : IsLocalRing (AdjoinRoot g) :=
      DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
        (g := g) hg hirr
    let _ : IsLocalHom (algebraMap R (AdjoinRoot g)) := by
      simpa only [AdjoinRoot.algebraMap_eq] using
        DVRResidue.adjoinRoot_isLocalHom_of_irreducible_map (g := g) hirr
    (DVRResidue.residueFieldAlgEquivAdjoinRootOfMapEq (g := g) gbar hirr hmap)
        (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (AdjoinRoot g)) x) =
      algebraMap (IsLocalRing.ResidueField R) (AdjoinRoot gbar) x := by
  dsimp only
  let _ : IsLocalRing (AdjoinRoot g) :=
    DVRResidue.adjoinRoot_isLocalRing_of_monic_of_irreducible_map
      (g := g) hg hirr
  have hLocMap : IsLocalHom (algebraMap R (AdjoinRoot g)) := by
    simpa only [AdjoinRoot.algebraMap_eq] using
      DVRResidue.adjoinRoot_isLocalHom_of_irreducible_map (g := g) hirr
  let _ : IsLocalHom (algebraMap R (AdjoinRoot g)) := hLocMap
  exact AlgEquiv.commutes _ _

end AlgEquivCompat
