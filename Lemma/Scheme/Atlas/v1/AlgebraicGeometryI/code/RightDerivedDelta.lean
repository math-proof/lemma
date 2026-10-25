import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RightDerivedDelta
open CategoryTheory CategoryTheory.Limits DerivedFunctorsDefs CohomologyConnection RightDerivedDelta
open DerivedFunctorsDefs CohomologyConnection


namespace RightDerivedDelta

/--
[effaceable_of_degree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RightDerivedDelta.lean)
-/
@[path]
lemma effaceable_of_degree_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [EnoughInjectives C]
  {F : C ⥤ D}
  [F.Additive]
  {δF : CohomDeltaFunctor C D}
-- given
  (h : ∀ n, δF.T n = F.rightDerived n) :
-- imply
  δF.IsEffaceable := by
-- proof
  intro n X
  obtain ⟨I, i, hi, hI⟩ := rightDerived_effaceable_at F n X
  exact ⟨I, i, hi, h (n + 1) ▸ hI⟩
section ExistenceTheorem
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type*} [Category D] [Abelian D]
end ExistenceTheorem
section NonSelfComparison
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type*} [Category D] [Abelian D]

end RightDerivedDelta


-- created on 2026-10-23
