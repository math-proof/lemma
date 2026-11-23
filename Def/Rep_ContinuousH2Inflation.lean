module

public import Mathlib
public import Def.Submodule_ContinuousH2
public import Instance.GroupCohomology_LevelSubgroup

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]

def levelInflate₁ :
    ((G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] (G → M) where
  toFun y g := (y (g : G ⧸ F.fixingSubgroup.comap r) : M)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelInflate₂ :
    ((G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) →
        M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] (G × G → M) where
  toFun x p := (x ((p.1 : G ⧸ F.fixingSubgroup.comap r), (p.2 : G ⧸ F.fixingSubgroup.comap r)) : M)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section lemmas

variable {r M F}

omit [Normal ℚ F] in
variable [FiniteDimensional ℚ F]

end lemmas

variable [FiniteDimensional ℚ F]

def levelInflateCocycles₂ :
    cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] levelCocycles₂ r M :=
  ((levelInflate₂ r M F).comp (Submodule.subtype _)).codRestrict _ fun x =>
    levelInflate₂_mem_levelCocycles₂ x.2

def continuousH2Inflation :
    H2 (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] continuousH2 r M :=
  let N := M.quotientToInvariants (F.fixingSubgroup.comap r)
  (LinearMap.ker (H2π N).hom).liftQ
      (continuousH2π r M ∘ₗ levelInflateCocycles₂ r M F)
      (fun x hx =>
        (continuousH2π_levelInflateCocycles₂_eq_zero r M F
          ((H2π_eq_zero_iff _).1 (by
            simpa [LinearMap.mem_ker] using hx)))) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective (H2π N).hom
      ((ModuleCat.epi_iff_surjective (H2π N)).1 inferInstance)).symm

end groupCohomology

end

end
