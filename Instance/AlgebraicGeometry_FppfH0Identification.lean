-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FppfH0Identification.lean: instance decls only.
import Mathlib.CategoryTheory.Sites.Continuous
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Instance.AlgebraicGeometry_FppfCohomologyLES
import Lemma.AlgebraicGeometry.FppfH0Identification

universe v' u' wE vE uE v₁ v₂ u₁ u₂ u w' w v

open CategoryTheory CategoryTheory.Limits Opposite


namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

instance (n : ℕ) : (fppfCohomologyFunctor S n).Additive :=
  inferInstanceAs (Sheaf.functorH (smallFppfTopology S) n).Additive


end AlgebraicGeometry.Scheme

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits Opposite AlgebraicGeometry FppfCohomologyLES

namespace EtaleCohomologyLES

instance etaleTopologySubcanonical : Scheme.etaleTopology.{u}.Subcanonical :=
  .of_le Scheme.etaleTopology_le_fppfTopology


section EtaleSite

instance etaleSheavesIsGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (Sheaf Scheme.etaleTopology.{u} Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} Scheme.{u} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall Scheme.etaleTopology Ab.{u + 1}


end EtaleSite

section EtaleFppfChangeOfTopology

instance idIsContinuousEtaleFppf :
    Functor.IsContinuous (𝟭 Scheme.{u}) Scheme.etaleTopology.{u} Scheme.fppfTopology.{u} :=
  isContinuous_id_of_le Scheme.etaleTopology_le_fppfTopology

instance : fppfSheafToEtaleSheaf.{u}.Faithful :=
  faithful_sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

instance : fppfSheafToEtaleSheaf.{u}.Full :=
  full_sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

instance : fppfSheafToEtaleSheaf.{u}.Additive :=
  additive_sheafInclusionOfLe Scheme.etaleTopology_le_fppfTopology

instance constSchemeOpAdditive :
    (Functor.const (Scheme.{u})ᵒᵖ : Ab.{u + 1} ⥤ ((Scheme.{u})ᵒᵖ ⥤ Ab.{u + 1})).Additive where
  map_add := by intros; ext; rfl

instance constantSheafEtaleAdditive :
    (constantSheaf Scheme.etaleTopology.{u} Ab.{u + 1}).Additive :=
  inferInstanceAs
    (Functor.const (Scheme.{u})ᵒᵖ ⋙ presheafToSheaf Scheme.etaleTopology.{u} Ab.{u + 1}).Additive

instance constantSheafFppfAdditive :
    (constantSheaf Scheme.fppfTopology.{u} Ab.{u + 1}).Additive :=
  inferInstanceAs
    (Functor.const (Scheme.{u})ᵒᵖ ⋙ presheafToSheaf Scheme.fppfTopology.{u} Ab.{u + 1}).Additive


end EtaleFppfChangeOfTopology


end EtaleCohomologyLES

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Limits

