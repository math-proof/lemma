import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme} {f : X ⟶ Spec (CommRingCat.of R)} [IsProper f]
-- given
  (hfin : (f.base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite) :
-- imply
  IsFinite f := by
-- proof
  classical
  have hqf : ∀ x : X, f.base x = IsLocalRing.closedPoint R → f.QuasiFiniteAt x := by
    intro x hx
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    let _ : Finite ↥(f.fiber (f.base x)) := by
      let _ : Finite ↥(f.base ⁻¹' {f.base x}) := by
        rw [hx]
        apply hfin.to_subtype
      exact Finite.of_equiv _ (f.fiberHomeo (f.base x)).toEquiv.symm
    let _ : LocallyOfFiniteType (f.fiberToSpecResidueField (f.base x)) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    let _ : LocallyQuasiFinite (f.fiberToSpecResidueField (f.base x)) :=
      LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => Set.toFinite _
    have hd := (f.fiberToSpecResidueField (f.base x)).isDiscrete_preimage_singleton
      ((f.fiberToSpecResidueField (f.base x)).base (f.asFiber x))
    have huniv : (f.fiberToSpecResidueField (f.base x)).base ⁻¹'
      {(f.fiberToSpecResidueField (f.base x)).base (f.asFiber x)} = Set.univ :=
      Set.eq_univ_of_forall fun z => Subsingleton.elim _ _
    rw [huniv, isDiscrete_univ_iff] at hd
    apply isOpen_discrete
  have htop : f.quasiFiniteLocus = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_contra hxU
    have hZ : IsClosed ((f.quasiFiniteLocus : Set X)ᶜ) := f.quasiFiniteLocus.2.isClosed_compl
    have hfZ : IsClosed (f.base '' (f.quasiFiniteLocus : Set X)ᶜ) := f.isClosedMap _ hZ
    have hmem : f.base x ∈ f.base '' (f.quasiFiniteLocus : Set X)ᶜ := ⟨x, hxU, rfl⟩
    have hcl : IsLocalRing.closedPoint R ∈ f.base '' (f.quasiFiniteLocus : Set X)ᶜ :=
      (IsLocalRing.specializes_closedPoint (f.base x)).mem_closed hfZ hmem
    obtain ⟨z, hz, hzc⟩ := hcl
    apply hz (hqf z hzc)
  let _ : LocallyQuasiFinite f := (Scheme.Hom.quasiFiniteLocus_eq_top_iff f).mp htop
  apply IsFinite.of_isProper_of_locallyQuasiFinite f


-- created on 2026-10-20
