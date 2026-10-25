-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_FppfSiteCohomology.lean: instance decls only.
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

instance : MorphismProperty.IsMultiplicative @LocallyOfFinitePresentation where
  id_mem _ := inferInstance


instance : fppfPrecoverage.{u}.HasIsos :=
  inferInstanceAs (Scheme.precoverage fppfProperty.{u}).HasIsos

instance : fppfPrecoverage.{u}.HasPullbacks :=
  inferInstanceAs (Scheme.precoverage fppfProperty.{u}).HasPullbacks


instance (S : Scheme.{u}) : Category.{u} S.Fppf :=
  inferInstanceAs <| Category.{u} (MorphismProperty.Over fppfProperty ⊤ S)

namespace Fppf

variable (S : Scheme.{u})

instance (U : S.Fppf) : Flat U.hom := U.prop.1
instance (U : S.Fppf) : LocallyOfFinitePresentation U.hom := U.prop.2


instance : (Fppf.forget S).Full :=
  inferInstanceAs (MorphismProperty.Over.forget _ _ _).Full

instance : (Fppf.forget S).Faithful :=
  inferInstanceAs (MorphismProperty.Over.forget _ _ _).Faithful

end Fppf


instance (S : Scheme.{u}) :
    (Fppf.forget S).LocallyCoverDense (fppfTopology.over S) :=
  inferInstanceAs <|
    (MorphismProperty.Over.forget fppfProperty ⊤ S).LocallyCoverDense
      (S.overGrothendieckTopology fppfProperty)


instance (S : Scheme.{u}) :
    (Fppf.forget S).IsCocontinuous (smallFppfTopology S) (fppfTopology.over S) :=
  inferInstanceAs <|
    (MorphismProperty.Over.forget fppfProperty ⊤ S).IsCocontinuous
      ((MorphismProperty.Over.forget fppfProperty ⊤ S).restrictedTopology
        (S.overGrothendieckTopology fppfProperty))
      (S.overGrothendieckTopology fppfProperty)

example (S : Scheme.{u}) : EssentiallySmall.{u + 1} S.Fppf := inferInstance


instance (S : Scheme.{u}) : HasTerminal S.Fppf :=
  (fppfTerminalIsTerminal S).hasTerminal

variable (S : Scheme.{u})

instance hasSheafify_smallFppfTopology : HasSheafify (smallFppfTopology S) Ab.{u + 1} :=
  inferInstance

noncomputable instance abelian_sheaf_smallFppfTopology :
    Abelian (Sheaf (smallFppfTopology S) Ab.{u + 1}) :=
  inferInstance

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

instance isGrothendieckAbelian_sheaf_smallFppfTopology :
    IsGrothendieckAbelian.{u + 1} (Sheaf (smallFppfTopology S) Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.Fppf := inferInstance
  exact IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel.{u + 1} S.Fppf).inverse.sheafInducedTopologyEquivOfIsCoverDense
      (smallFppfTopology S) Ab.{u + 1})

instance hasExt_sheaf_smallFppfTopology :
    HasExt.{u + 1} (Sheaf (smallFppfTopology S) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasExt _


noncomputable instance (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (n : ℕ) :
    AddCommGroup (fppfCohomology S F n) :=
  inferInstanceAs <| AddCommGroup (F.H n)

instance : (Functor.const (S.Fppf)ᵒᵖ : Ab.{u + 1} ⥤ ((S.Fppf)ᵒᵖ ⥤ Ab.{u + 1})).Additive where
  map_add := by intros; ext; rfl

instance : (constantSheaf (smallFppfTopology S) Ab.{u + 1}).Additive :=
  inferInstanceAs
    (Functor.const (S.Fppf)ᵒᵖ ⋙ presheafToSheaf (smallFppfTopology S) Ab.{u + 1}).Additive

universe w in


end AlgebraicGeometry.Scheme
