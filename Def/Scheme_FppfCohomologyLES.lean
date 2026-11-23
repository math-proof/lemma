module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.Fintype.Units
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Instance.AlgebraicGeometry_FppfCohomologyLES
public import Abbrev.AlgebraicGeometry_FppfCohomologyLES

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

variable {J}

noncomputable def cohomologyMap {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (n : ℕ) :
    F.H n →+ G.H n :=
  (Ext.mk₀ φ).postcomp (constIntSheaf J) (add_zero n)

noncomputable def cohomologyδ {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.X₃.H n₀ →+ S.X₁.H n₁ :=
  hS.extClass.postcomp (constIntSheaf J) h

noncomputable def cohomologyComposableArrows {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w'} 5 :=
  Ext.covariantSequence (constIntSheaf J) hS n₀ n₁ h

noncomputable def cohomologyZeroAddEquivHom (F : Sheaf J AddCommGrpCat.{w}) :
    F.H 0 ≃+ (constIntSheaf J ⟶ F) :=
  Ext.addEquiv₀

noncomputable def biprodSES (F G : Sheaf J AddCommGrpCat.{w}) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (biprod.inl : F ⟶ F ⊞ G) (biprod.snd : F ⊞ G ⟶ G) (by simp)

end GenericSite

section FppfSite

open AlgebraicGeometry Scheme

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

noncomputable def fppfCohomologyZeroAddEquivHom (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    FppfH F 0 ≃+ (constIntSheaf Scheme.fppfTopology.{u} ⟶ F) :=
  cohomologyZeroAddEquivHom F

end WithLocalInstances

end FppfSite


end FppfCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

noncomputable def cohomologyMapAddEquiv {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) (n : ℕ) :
    F.H n ≃+ G.H n where
  toFun := cohomologyMap e.hom n
  invFun := cohomologyMap e.inv n
  left_inv x := by rw [← cohomologyMap_comp, Iso.hom_inv_id, cohomologyMap_id]
  right_inv x := by rw [← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id]
  map_add' x y := map_add (cohomologyMap e.hom n) x y

noncomputable def biprodSESHom (F : Sheaf J AddCommGrpCat.{w})
    {G G' : Sheaf J AddCommGrpCat.{w}} (ψ : G ⟶ G') :
    biprodSES F G ⟶ biprodSES F G' where
  τ₁ := 𝟙 F
  τ₂ := biprod.map (𝟙 F) ψ
  τ₃ := ψ
  comm₁₂ := by simp [biprodSES]
  comm₂₃ := by simp [biprodSES]

noncomputable def biprodSESSwap (F G : Sheaf J AddCommGrpCat.{w}) :
    ShortComplex (Sheaf J AddCommGrpCat.{w}) :=
  ShortComplex.mk (biprod.inr : F ⟶ G ⊞ F) (biprod.fst : G ⊞ F ⟶ G) (by simp)

noncomputable def biprodSESSwapIso (F G : Sheaf J AddCommGrpCat.{w}) :
    biprodSES F G ≅ biprodSESSwap F G :=
  ShortComplex.isoMk (Iso.refl F) (biprod.braiding F G) (Iso.refl G)
    (by
      dsimp [biprodSES, biprodSESSwap]
      apply biprod.hom_ext <;> simp)
    (by
      dsimp [biprodSES, biprodSESSwap]
      simp)

end GenericSite

section FppfSite

open AlgebraicGeometry Scheme

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

end WithLocalInstances

end FppfSite

end FppfCohomologyLES

end
