import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
open CategoryTheory MonoidalCategory


namespace TensorCategories

/--
[fpDimFunction_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_45_11.lean)
-/
@[path]
lemma fpDimFunction_unique
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [hGR : HasGrothendieckFusionRing C]
-- given
  (d₁ d₂ : FPdimFunction (C := C)) :
-- imply
  ∀ (X : C), d₁.fpDim X = d₂.fpDim X := by
-- proof
  letI := hGR.ι_decidableEq
  letI := hGR.ι_fintype
  letI := hGR.ι_nonempty
  letI := hGR.ι_hasPF
  obtain ⟨fpd⟩ := hGR.fusionRing.exists_FPdimData
  intro X
  rw [hGR.fpDimFunction_eq fpd d₁ X, hGR.fpDimFunction_eq fpd d₂ X]

end TensorCategories

namespace TensorCategories

/--
[corollary_1_45_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_45_11.lean)
-/
@[path]
lemma corollary_1_45_11
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [RigidCategory C]
  {D : Type u₁}
  [Category.{v₁} D]
  [MonoidalCategory D]
  [Abelian D]
  [RigidCategory D]
  [hC : HasGrothendieckFusionRing C]
  [hD : HasGrothendieckFusionRing D]
  {QTF : QuasiTensorFunctor k C D}
-- given
  (dC : FPdimFunction (C := C))
  (dD : FPdimFunction (C := D)) :
-- imply
  ∀ (X : C), dD.fpDim (QTF.F.obj X) = dC.fpDim X := by
-- proof
  let dComp : FPdimFunction (C := C) :=
  { fpDim := fun X => dD.fpDim (QTF.F.obj X)
    fpDim_unit := by
      have hiso : Nonempty (QTF.F.obj (𝟙_ C) ≅ 𝟙_ D) := ⟨QTF.unitIso⟩
      rw [dD.fpDim_iso _ _ hiso, dD.fpDim_unit]
    fpDim_pos := fun X => dD.fpDim_pos (QTF.F.obj X)
    fpDim_tensor := fun X Y => by
      have hiso : Nonempty (QTF.F.obj (X ⊗ Y) ≅ QTF.F.obj X ⊗ QTF.F.obj Y) :=
        ⟨(QTF.J X Y).symm⟩
      rw [dD.fpDim_iso _ _ hiso, dD.fpDim_tensor]
    fpDim_iso := fun X Y hXY => by
      have hFiso : Nonempty (QTF.F.obj X ≅ QTF.F.obj Y) :=
        hXY.map (fun e => QTF.F.mapIso e)
      exact dD.fpDim_iso _ _ hFiso }
  intro X
  exact fpDimFunction_unique dComp dC X

end TensorCategories


-- created on 2026-10-23
