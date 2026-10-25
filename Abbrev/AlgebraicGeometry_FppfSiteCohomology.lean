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


abbrev fppfProperty : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation


section SpecInt

noncomputable abbrev specInt : Scheme.{0} := Spec (CommRingCat.of ℤ)

end SpecInt

end AlgebraicGeometry.Scheme
