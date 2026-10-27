import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.DerivedFunctorsConsolidation
open CategoryTheory CategoryTheory.Limits DerivedFunctorsDefs CohomologyConnection
open DerivedFunctorsDefs CohomologyConnection


/--
[rightDerived_injective_is_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsConsolidation.lean)
-/
@[path]
lemma rightDerived_injective_is_zero
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [EnoughInjectives C]
  {F : C ⥤ D}
  [F.Additive]
  {n : ℕ}
  {X : C}
  [Injective X]
-- given
  (hn : 0 < n) :
-- imply
  IsZero ((F.rightDerived n).obj X) := by
-- proof
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact F.isZero_rightDerived_obj_injective_succ k X
section PartC
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type*} [Category D] [Abelian D]

/--
[effaceable_implies_universal_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsConsolidation.lean)
-/
@[path]
lemma effaceable_implies_universal_uniqueness
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {T : CohomDeltaFunctor C D}
-- given
  (hT : T.IsEffaceable) :
-- imply
  ∀ (G : CohomDeltaFunctor C D) (m₁ m₂ : T.Morphism G), m₁.η 0 = m₂.η 0 → ∀ n, m₁.η n = m₂.η n :=
-- proof
  fun G m₁ m₂ h₀ => effaceable_morphism_unique T G hT m₁ m₂ h₀

/--
[effaceable_implies_universal_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsConsolidation.lean)
-/
@[path]
lemma effaceable_implies_universal_existence
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {T : CohomDeltaFunctor C D}
-- given
  (hT : T.IsEffaceable) :
-- imply
  ∀ (G : CohomDeltaFunctor C D) (η₀ : T.T 0 ⟶ G.T 0), ∃ (m : T.Morphism G), m.η 0 = η₀ :=
-- proof
  fun G η₀ =>
    effaceable_morphism_exists T G hT.toIsEffaceableMorphism η₀

/--
[effaceable_implies_universal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsConsolidation.lean)
-/
@[path]
lemma effaceable_implies_universal
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {T : CohomDeltaFunctor C D}
-- given
  (hT : T.IsEffaceable) :
-- imply
  T.IsUniversal where extend :=
-- proof
  effaceable_implies_universal_existence T hT
    unique := effaceable_implies_universal_uniqueness T hT
section PartE
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type*} [Category D] [Abelian D]
end PartE


-- created on 2026-10-23
