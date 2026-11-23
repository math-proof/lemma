import Mathlib.CategoryTheory.Sites.Continuous
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Def.Scheme_FppfCohomologyLES
import Instance.AlgebraicGeometry_FppfH0Identification
import Abbrev.AlgebraicGeometry_FppfH0Identification

universe v' u' wE vE uE v₁ v₂ u₁ u₂ u w' w v

open CategoryTheory CategoryTheory.Limits Opposite


namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

open Abelian in

open Abelian in

open Abelian in

open Abelian in

open Abelian in

open Abelian in

noncomputable def fppfH0SectionsIsoApp (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) :
    (fppfCohomologyFunctor S 0).obj F ≅ F.obj.obj (op (fppfTerminal S)) :=
  AddEquiv.toAddCommGrpIso
    (X := (fppfCohomologyFunctor S 0).obj F)
    (Y := F.obj.obj (op (fppfTerminal S)))
    (fppfCohomologyZeroAddEquiv S F)

noncomputable def fppfCohomologyZeroNatIso :
    fppfCohomologyFunctor S 0 ≅
      (sheafSections (smallFppfTopology S) Ab.{u + 1}).obj (op (fppfTerminal S)) :=
  NatIso.ofComponents (fun F => fppfH0SectionsIsoApp S F)
    (fun φ => fppfH0SectionsIsoApp_naturality S φ)


section SpecInt

noncomputable def fppfCohomologySpecIntZeroNatIso :
    fppfCohomologyFunctor specInt 0 ≅
      (sheafSections (smallFppfTopology specInt) Ab.{1}).obj (op (fppfTerminal specInt)) :=
  fppfCohomologyZeroNatIso specInt

end SpecInt

end AlgebraicGeometry.Scheme

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits Opposite AlgebraicGeometry FppfCohomologyLES Scheme

namespace EtaleCohomologyLES

section GenericChangeOfTopology

variable {C : Type u} [Category.{v} C]

def sheafInclusionOfLe {A : Type u₂} [Category.{v₂} A] {J K : GrothendieckTopology C}
    (hJK : J ≤ K) : Sheaf K A ⥤ Sheaf J A where
  obj F := ⟨F.obj, F.property.of_le hJK⟩
  map φ := ObjectProperty.homMk φ.hom
  map_id _ := Sheaf.hom_ext rfl
  map_comp _ _ := Sheaf.hom_ext rfl

variable {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

noncomputable def sheafHZeroSectionsAddEquiv [(constantSheaf J AddCommGrpCat.{w}).Additive]
    {T : C} (hT : IsTerminal T) (G : Sheaf J AddCommGrpCat.{w}) :
    G.H 0 ≃+ G.obj.obj (op T) :=
  ((cohomologyZeroAddEquivHom G).trans
    ((constantSheafAdj J AddCommGrpCat.{w} hT).homAddEquiv _ _)).trans
    (Scheme.homULiftIntAddEquiv.{w} (G.obj.obj (op T)))

noncomputable def sheafInclusionHZeroAddEquiv {K : GrothendieckTopology C} (hJK : J ≤ K)
    [HasSheafify K AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf K AddCommGrpCat.{w})]
    [(constantSheaf J AddCommGrpCat.{w}).Additive]
    [(constantSheaf K AddCommGrpCat.{w}).Additive]
    {T : C} (hT : IsTerminal T) (F : Sheaf K AddCommGrpCat.{w}) :
    ((sheafInclusionOfLe (A := AddCommGrpCat.{w}) hJK).obj F).H 0 ≃+ F.H 0 :=
  (sheafHZeroSectionsAddEquiv hT ((sheafInclusionOfLe hJK).obj F)).trans
    (sheafHZeroSectionsAddEquiv hT F).symm

end GenericChangeOfTopology

section EtaleSite

section WithLocalInstances

variable [HasSheafify Scheme.etaleTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})]

noncomputable def etaleCohomologyZeroAddEquivHom
    (F : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) :
    EtaleH F 0 ≃+ (constIntSheaf Scheme.etaleTopology.{u} ⟶ F) :=
  cohomologyZeroAddEquivHom F

noncomputable def etaleCohomologyFunctor (n : ℕ) :
    Sheaf Scheme.etaleTopology.{u} Ab.{u + 1} ⥤ Ab.{u + 1} :=
  Sheaf.functorH Scheme.etaleTopology.{u} n


end WithLocalInstances

end EtaleSite

section EtaleFppfChangeOfTopology

noncomputable def fppfSheafToEtaleSheaf :
    Sheaf Scheme.fppfTopology.{u} Ab.{u + 1} ⥤ Sheaf Scheme.etaleTopology.{u} Ab.{u + 1} :=
  sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

section WithLocalInstances

variable [HasSheafify Scheme.etaleTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1})]
  [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

noncomputable def etaleHZeroSectionsAddEquiv {T : Scheme.{u}} (hT : IsTerminal T)
    (G : Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) :
    G.H 0 ≃+ G.obj.obj (op T) :=
  sheafHZeroSectionsAddEquiv hT G

noncomputable def fppfHZeroSectionsAddEquiv {T : Scheme.{u}} (hT : IsTerminal T)
    (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    F.H 0 ≃+ F.obj.obj (op T) :=
  sheafHZeroSectionsAddEquiv hT F

noncomputable def fppfToEtaleHZeroAddEquiv {T : Scheme.{u}} (hT : IsTerminal T)
    (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :
    (fppfSheafToEtaleSheaf.{u}.obj F).H 0 ≃+ F.H 0 :=
  sheafInclusionHZeroAddEquiv Scheme.etaleTopology_le_fppfTopology hT F

end WithLocalInstances

end EtaleFppfChangeOfTopology

section SpecInt

noncomputable def etaleHZeroSpecIntAddEquiv (G : Sheaf Scheme.etaleTopology.{0} Ab.{1}) :
    G.H 0 ≃+ G.obj.obj (op (Spec (CommRingCat.of ℤ))) :=
  etaleHZeroSectionsAddEquiv specZIsTerminal G

noncomputable def fppfToEtaleHZeroSpecIntAddEquiv
    (F : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    (fppfSheafToEtaleSheaf.{0}.obj F).H 0 ≃+ F.H 0 :=
  fppfToEtaleHZeroAddEquiv specZIsTerminal F


end SpecInt

end EtaleCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section GenericSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

noncomputable def homPostcompAddEquiv {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G) :
    (constIntSheaf J ⟶ F) ≃+ (constIntSheaf J ⟶ G) where
  toFun a := a ≫ e.hom
  invFun b := b ≫ e.inv
  left_inv a := by
    show (a ≫ e.hom) ≫ e.inv = a
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv b := by
    show (b ≫ e.inv) ≫ e.hom = b
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  map_add' a b := by
    show (a + b) ≫ e.hom = a ≫ e.hom + b ≫ e.hom
    rw [Preadditive.add_comp]

end GenericSite

section FppfSite

open AlgebraicGeometry Scheme

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

end WithLocalInstances

end FppfSite

end FppfCohomologyLES
