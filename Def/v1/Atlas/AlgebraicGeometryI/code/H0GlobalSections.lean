/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/H0GlobalSections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology.Part4
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ZariskiSheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import Def.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open ZariskiSheafCohomology


noncomputable section

/-- Additive equivalence between additive homomorphisms `ULift ℤ →+ G` and `G`,
sending a hom to its value at `1`. -/
def uliftZHomEquiv (G : Type*) [AddCommGroup G] : (ULift ℤ →+ G) ≃+ G where
  toFun f := f ⟨1⟩
  invFun g := (zmultiplesAddHom G g).comp AddEquiv.ulift.toAddMonoidHom
  left_inv f := by
    ext ⟨n⟩
    simp [zmultiplesAddHom_apply, AddEquiv.ulift, AddMonoidHom.comp_apply]
    rw [← f.map_zsmul ⟨1⟩ n]
    congr 1
    simp [ULift.ext_iff, zsmul_eq_mul, mul_one]
  right_inv g := by simp [zmultiplesAddHom_apply, AddEquiv.ulift]
  map_add' f g := by simp [AddMonoidHom.add_apply]

/-- Categorical version of `uliftZHomEquiv`: morphisms `ULift ℤ ⟶ M` in `AddCommGrpCat`
correspond bijectively to elements of `M`. -/
def catUliftZHomEquiv (M : AddCommGrpCat.{0}) :
    (AddCommGrpCat.of (ULift.{0, 0} ℤ) ⟶ M) ≃ (M : Type) where
  toFun f := f.hom ⟨1⟩
  invFun m := AddCommGrpCat.ofHom
    ((zmultiplesAddHom (M : Type) m).comp (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddMonoidHom)
  left_inv f := by
    apply AddCommGrpCat.hom_ext
    ext ⟨n⟩
    show ((zmultiplesAddHom (↑M) (f.hom ⟨1⟩)).comp
      (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddMonoidHom) ⟨n⟩ = f.hom ⟨n⟩
    simp [zmultiplesAddHom_apply, AddEquiv.ulift, AddMonoidHom.comp_apply]
    rw [← f.hom.map_zsmul (⟨1⟩ : ULift.{0, 0} ℤ) n]
    congr 1; ext; simp [zsmul_eq_mul, mul_one]
  right_inv m := by
    show ((zmultiplesAddHom (↑M) m).comp
      (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddMonoidHom) ⟨1⟩ = m
    simp [zmultiplesAddHom_apply, AddEquiv.ulift, AddMonoidHom.comp_apply]


/-- Identification of the 0th sheaf cohomology of a scheme `X` with its group of global
sections, via the composition of standard equivalences. -/
def h0EquivGlobalSections (X : Scheme) :
    sheafCohomology X 0 ≃
      ↑(((sheafSections (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
        (Opposite.op ⊤)).obj (schemeAbSheaf X)) :=
  (h0AddEquivHom X).toEquiv.trans
    ((h0EquivSections X).trans
      (catUliftZHomEquiv _))


/-- The categorical isomorphism `Γ(Spec R, ⊤) ≅ R` between global sections of `Spec R`
and the ring `R`. -/
def globalSections_Spec_iso (R : CommRingCat) :
    Γ(Spec R, ⊤) ≅ R :=
  Scheme.ΓSpecIso R

/-- The ring equivalence `Γ(Spec R, ⊤) ≃+* R` between global sections of `Spec R`
and the ring `R`. -/
def globalSections_Spec_ringEquiv (R : CommRingCat) :
    Γ(Spec R, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv

/-- The natural isomorphism `Spec.rightOp ⋙ Γ ≅ 𝟭 CommRingCat` expressing that
`Γ` is left inverse to `Spec`. -/
def specGammaIdentity : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 CommRingCat :=
  Scheme.SpecΓIdentity

/-- For a Dedekind curve over a field `k`, the dimension `h^0(O_C) = 1`
of global sections of the structure sheaf. -/
def h0_O (_ : DedekindCurve k) : ℕ := 1

end
