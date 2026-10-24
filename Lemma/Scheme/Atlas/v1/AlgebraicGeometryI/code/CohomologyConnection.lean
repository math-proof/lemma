import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CohomologyConnection
open CategoryTheory CategoryTheory.Limits SheafCohomology CohomologyP1 DerivedFunctorsDefs CohomologyConnection
open SheafCohomology CohomologyP1 DerivedFunctorsDefs


namespace CohomologyConnection

/--
[CechToDerivedData.morphisms_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyConnection.lean)
-/
@[path]
lemma CechToDerivedData.morphisms_unique
  {C : Type u₁}
  [Category.{v₁} C]
  [Abelian C]
  {m₁ m₂ : data.cech.Morphism data.derived}
-- given
  (data : CechToDerivedData (C := C) (D := D))
  (h₀ : m₁.η 0 = m₂.η 0) :
-- imply
  ∀ n, m₁.η n = m₂.η n :=
-- proof
  effaceable_morphism_unique data.cech data.derived data.cech_effaceable m₁ m₂ h₀

end CohomologyConnection

namespace CohomologyConnection

/--
[CechDerivedComparison.comparison_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyConnection.lean)
-/
@[path]
lemma CechDerivedComparison.comparison_unique
  {C : Type u₁}
  [Category.{v₁} C]
  [Abelian C]
  {m : comp.cech.Morphism comp.derived}
-- given
  (comp : CechDerivedComparison (C := C) (D := D))
  (h₀ : m.η 0 = comp.comparison.η 0) :
-- imply
  ∀ n, m.η n = comp.comparison.η n :=
-- proof
  comp.toCechToDerivedData.morphisms_unique m comp.comparison h₀

end CohomologyConnection

namespace CohomologyConnection

/--
[CechDerivedIsomorphism.forward_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyConnection.lean)
-/
@[path]
lemma CechDerivedIsomorphism.forward_unique
  {C : Type u₁}
  [Category.{v₁} C]
  [Abelian C]
  {m : iso.cech.Morphism iso.derived}
-- given
  (iso : CechDerivedIsomorphism (C := C) (D := D))
  (h₀ : m.η 0 = iso.forward.η 0) :
-- imply
  ∀ n, m.η n = iso.forward.η n :=
-- proof
  iso.toCechToDerivedData.morphisms_unique m iso.forward h₀

end CohomologyConnection

namespace CohomologyConnection

/--
[CechDerivedIsomorphism.backward_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyConnection.lean)
-/
@[path]
lemma CechDerivedIsomorphism.backward_unique
  {C : Type u₁}
  [Category.{v₁} C]
  [Abelian C]
  {m : iso.derived.Morphism iso.cech}
-- given
  (iso : CechDerivedIsomorphism (C := C) (D := D))
  (h₀ : m.η 0 = iso.backward.η 0) :
-- imply
  ∀ n, m.η n = iso.backward.η n :=
-- proof
  effaceable_morphism_unique iso.derived iso.cech iso.derived_effaceable m iso.backward h₀
end FullConnection
section DerivedFacts
universe v₂ u₂
variable {C : Type u₂} [Category.{v₂} C] [Abelian C]
  {D : Type*} [Category D] [Abelian D]
end DerivedFacts

end CohomologyConnection


-- created on 2026-10-23
