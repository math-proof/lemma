module
public import Mathlib
public import Def.Submodule_ContinuousUnramifiedLevel
public import Instance.GroupCohomology_LevelSubgroup
public import Def.Rep_ContinuousH2Inflation
set_option autoImplicit false
open CategoryTheory


public section

noncomputable section
namespace groupCohomology

section A0
variable {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (M : Rep.{0} k G) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]

omit [Normal ℚ F] in
def levelInflateCocyclesSr₂ (hF : F.IsUnramifiedOutside S) :
    cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] ↥(levelCocyclesSr₂ r S M) :=
  ((levelInflate₂ r M F).comp (Submodule.subtype _)).codRestrict _ fun x => levelInflate₂_mem_levelCocyclesSr₂ r S M F hF x.2

def continuousH2SrInflation (hF : F.IsUnramifiedOutside S) :
    H2 (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] continuousH2Sr r S M :=
  let N := M.quotientToInvariants (F.fixingSubgroup.comap r)
  (LinearMap.ker (H2π N).hom).liftQ
      (continuousH2Srπ r S M ∘ₗ levelInflateCocyclesSr₂ r S M F hF)
      (fun x hx =>
        (continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero r S M F hF
          ((H2π_eq_zero_iff _).1 (by
            simpa [LinearMap.mem_ker] using hx)))) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective (H2π N).hom
      ((ModuleCat.epi_iff_surjective (H2π N)).1 inferInstance)).symm

end A0

end groupCohomology
end
