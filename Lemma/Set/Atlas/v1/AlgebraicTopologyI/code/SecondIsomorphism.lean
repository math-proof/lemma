import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.SecondIsomorphism
open CategoryTheory CategoryTheory.Limits SecondIsomorphism


namespace SecondIsomorphism

variable [Category C] [Abelian C]
variable {A B X : C} (f : A ⟶ X) (g : B ⟶ X)
variable [Mono f] [Mono g]
/--
[pullbackIsoKernelOfDesc_hom_ι](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SecondIsomorphism.lean)
-/
@[path]
omit [Mono f] [Mono g] in
is the biproduct lift `⟨π₁, −π₂⟩` of the pullback projections. -/
lemma pullbackIsoKernelOfDesc_hom_ι :
  (pullbackIsoKernelOfDesc f g).hom ≫ kernel.ι _ =
    biprod.lift (pullback.fst f g) (-pullback.snd f g) :=
  kernel.lift_ι _ _ _
set_option maxHeartbeats 800000 in
set_option linter.unusedSectionVars false in

end SecondIsomorphism

namespace SecondIsomorphism

/--
[isPushout_pullback_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SecondIsomorphism.lean)
-/
@[path]
lemma isPushout_pullback_image
  [Category C]
  [Abelian C]
  {A B X : C}
  {f : A ⟶ X}
  {g : B ⟶ X}
  [Mono f]
  [Mono g] :
-- imply
  IsPushout (pullback.fst f g) (pullback.snd f g) (biprod.inl ≫ factorThruImage (biprod.desc f g)) (biprod.inr ≫ factorThruImage (biprod.desc f g)) := by
-- proof
  have w : pullback.fst f g ≫ biprod.inl ≫ factorThruImage (biprod.desc f g) =
    pullback.snd f g ≫ biprod.inr ≫ factorThruImage (biprod.desc f g) := by
    apply (cancel_mono (image.ι (biprod.desc f g))).mp
    simp only [Category.assoc, image.fac, biprod.inl_desc, biprod.inr_desc, pullback.condition]
  refine IsPushout.mk ⟨w⟩ ⟨?_⟩
  refine PushoutCocone.IsColimit.mk _
    (fun s =>
      have hk : kernel.ι (biprod.desc f g) ≫ biprod.desc s.inl s.inr = 0 := by
        have : kernel.ι (biprod.desc f g) =
          (pullbackIsoKernelOfDesc f g).inv ≫
            (pullbackIsoKernelOfDesc f g).hom ≫ kernel.ι _ := by
          rw [Iso.inv_hom_id_assoc]
        rw [this, Category.assoc, pullbackIsoKernelOfDesc_hom_ι, biprod.lift_desc,
          Preadditive.neg_comp, s.condition, add_neg_cancel, comp_zero]
      (Abelian.coimageIsoImage' (biprod.desc f g)).inv ≫
        cokernel.desc (kernel.ι (biprod.desc f g)) (biprod.desc s.inl s.inr) hk)
    (fun s => by
      rw [Category.assoc, ← Category.assoc (factorThruImage _),
        Abelian.factorThruImage_comp_coimageIsoImage'_inv, cokernel.π_desc, biprod.inl_desc])
    (fun s => by
      rw [Category.assoc, ← Category.assoc (factorThruImage _),
        Abelian.factorThruImage_comp_coimageIsoImage'_inv, cokernel.π_desc, biprod.inr_desc])
    (fun s m h₁ h₂ => by
      apply (cancel_epi (factorThruImage (biprod.desc f g))).mp
      rw [← Category.assoc, Abelian.factorThruImage_comp_coimageIsoImage'_inv, cokernel.π_desc]
      have t := biprod.total (X := A) (Y := B)
      calc factorThruImage (biprod.desc f g) ≫ m
        = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫
          factorThruImage (biprod.desc f g) ≫ m := by rw [t, Category.id_comp]
        _ = biprod.fst ≫ ((biprod.inl ≫ factorThruImage (biprod.desc f g)) ≫ m) +
          biprod.snd ≫ ((biprod.inr ≫ factorThruImage (biprod.desc f g)) ≫ m) := by
            simp only [Preadditive.add_comp, Category.assoc]
        _ = biprod.fst ≫ s.inl + biprod.snd ≫ s.inr := by rw [h₁, h₂]
        _ = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫
          biprod.desc s.inl s.inr := by
            simp only [Preadditive.add_comp, Category.assoc, biprod.inl_desc, biprod.inr_desc]
        _ = biprod.desc s.inl s.inr := by rw [t, Category.id_comp])
end


/--
[kernelDesc_pullback_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SecondIsomorphism.lean)
-/
@[path]
private lemma kernelDesc_pullback_condition_eq
  [Category C]
  [Abelian C]
  {A B X : C}
  {f : A ⟶ X}
  {g : B ⟶ X} :
-- imply
  (kernel.ι (biprod.desc f g) ≫ biprod.fst) ≫ f = (-(kernel.ι (biprod.desc f g) ≫ biprod.snd)) ≫ g := by
-- proof
  apply SecondIsomorphism.kernelDesc_pullback_condition f g

/--
[pullbackIsoKernelOfDesc_hom_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SecondIsomorphism.lean)
-/
@[path]
private lemma pullbackIsoKernelOfDesc_hom__eq
  [Category C]
  [Abelian C]
  {A B X : C}
  {f : A ⟶ X}
  {g : B ⟶ X}
  [Mono f]
  [Mono g] :
-- imply
  (pullbackIsoKernelOfDesc f g).hom ≫ kernel.ι _ = biprod.lift (pullback.fst f g) (-pullback.snd f g) := by
-- proof
  apply SecondIsomorphism.pullbackIsoKernelOfDesc_hom_ f g


-- created on 2026-10-23
