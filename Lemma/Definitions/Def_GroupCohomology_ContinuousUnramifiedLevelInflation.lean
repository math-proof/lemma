import Mathlib
import Lemma.Definitions.Def_GroupCohomology_ContinuousUnramified
import Lemma.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Lemma.Definitions.Def_GroupCohomology_LevelSubgroup
import Lemma.Definitions.Def_GroupCohomology_ContinuousH2Inflation

set_option autoImplicit false

open CategoryTheory

noncomputable section
namespace groupCohomology

section A0
variable {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (M : Rep.{0} k G) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]

omit [Normal ℚ F] in
private lemma coe_mul_eq_of_mem' {g s : G} (hs : r s ∈ F.fixingSubgroup) :
    ((g * s : G) : G ⧸ F.fixingSubgroup.comap r) = (g : G ⧸ F.fixingSubgroup.comap r) := by
  rw [QuotientGroup.eq]; simpa using (F.fixingSubgroup.comap r).inv_mem hs

lemma levelInflate₁_mem_levelCochainsSr₁ (hF : F.IsUnramifiedOutside S) (y : (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) :
    levelInflate₁ r M F y ∈ levelCochainsSr₁ r S M :=
  ⟨F, hF, fun g s hs => by simp only [levelInflate₁_apply, coe_mul_eq_of_mem' r F hs]⟩

lemma levelInflate₂_mem_levelCocyclesSr₂ (hF : F.IsUnramifiedOutside S)
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCocyclesSr₂ r S M :=
  ⟨levelInflate₂_mem_cocycles₂ hx, ⟨F, hF, fun g g' s s' hs hs' => by
    simp only [levelInflate₂_apply, coe_mul_eq_of_mem' r F hs, coe_mul_eq_of_mem' r F hs']⟩⟩

lemma levelInflate₂_mem_levelCoboundariesSr₂ (hF : F.IsUnramifiedOutside S)
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCoboundariesSr₂ r S M := by
  obtain ⟨y, rfl⟩ := hx
  exact (mem_levelCoboundariesSr₂_iff r S M _).2 ⟨levelInflate₁ r M F y, levelInflate₁_mem_levelCochainsSr₁ r S M F hF y, (levelInflate₂_d₁₂ y).symm⟩

def levelInflateCocyclesSr₂ (hF : F.IsUnramifiedOutside S) :
    cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] ↥(levelCocyclesSr₂ r S M) :=
  ((levelInflate₂ r M F).comp (Submodule.subtype _)).codRestrict _ fun x => levelInflate₂_mem_levelCocyclesSr₂ r S M F hF x.2

lemma coe_levelInflateCocyclesSr₂ (hF : F.IsUnramifiedOutside S) (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    (levelInflateCocyclesSr₂ r S M F hF x : G × G → M) = levelInflate₂ r M F x := rfl

lemma continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero (hF : F.IsUnramifiedOutside S)
    {x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))}
    (hx : (x : _ → _) ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) = 0 :=
  (continuousH2Srπ_eq_zero_iff r S M _).2 (levelInflate₂_mem_levelCoboundariesSr₂ r S M F hF hx)

def continuousH2SrInflation (hF : F.IsUnramifiedOutside S) :
    H2 (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] continuousH2Sr r S M :=
  (Submodule.liftQ _ (continuousH2Srπ r S M ∘ₗ levelInflateCocyclesSr₂ r S M F hF) (by
      rintro x ⟨y, rfl⟩
      exact continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero r S M F hF ⟨y, rfl⟩))
    ∘ₗ (H2Iso (M.quotientToInvariants (F.fixingSubgroup.comap r))).hom.hom

lemma continuousH2SrInflation_H2π (hF : F.IsUnramifiedOutside S) (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2SrInflation r S M F hF (H2π _ x) = continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) := by
  have h := π_comp_H2Iso_hom_apply (M.quotientToInvariants (F.fixingSubgroup.comap r)) ((isoCocycles₂ _).inv x)
  simp only [Iso.inv_hom_id_apply] at h
  have e : (H2Iso (M.quotientToInvariants (F.fixingSubgroup.comap r))).hom.hom (H2π _ x)
      = (LinearMap.range (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).mkQ x :=
    Eq.trans rfl h
  have key : ∀ z, z = (LinearMap.range (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).mkQ x →
      (LinearMap.range (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).liftQ
          (continuousH2Srπ r S M ∘ₗ levelInflateCocyclesSr₂ r S M F hF)
          (by rintro x ⟨y, rfl⟩; exact continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero r S M F hF ⟨y, rfl⟩) z
        = continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) := by
    rintro _ rfl; rfl
  exact key _ e

end A0

end groupCohomology
end
