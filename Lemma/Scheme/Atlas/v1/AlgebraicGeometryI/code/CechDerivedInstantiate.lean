import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate.Part2
open CategoryTheory CategoryTheory.Limits SheafCohomology CohomologyP1 DerivedFunctorsDefs CohomologyConnection
open SheafCohomology CohomologyP1 DerivedFunctorsDefs


namespace DerivedFunctorsDefs

variable {C : Type u₀} [Category.{v₀} C] [Abelian C] [Category D] [Abelian D]
/--
[idMorphism_η](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean)
-/
@[path]
identity. -/
@[simp]
lemma CohomDeltaFunctor.idMorphism_η (F : CohomDeltaFunctor C D) (n : ℕ) :
  F.idMorphism.η n = 𝟙 (F.T n) :=
  rfl
end DerivedFunctorsDefs
namespace CohomologyConnection
section RightDerivedEffaceability
universe v₂ u₂
variable {C' : Type u₂} [Category.{v₂} C'] [Abelian C'] [EnoughInjectives C']
  {D' : Type*} [Category D'] [Abelian D']


namespace CohomologyConnection

/--
[rightDerived_effaceable_at](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean)
-/
@[path]
lemma rightDerived_effaceable_at
  {C' : Type u₂}
  [Category.{v₂} C']
  [Abelian C']
  [EnoughInjectives C']
  {F : C' ⥤ D'}
  [F.Additive]
  {n : ℕ}
  {X : C'} :
-- imply
  ∃ (I : C') (i : X ⟶ I), Mono i ∧ IsZero ((F.rightDerived (n + 1)).obj I) := by
-- proof
  obtain ⟨pres⟩ := EnoughInjectives.presentation X
  exact ⟨pres.J, pres.f, pres.mono, F.isZero_rightDerived_obj_injective_succ n pres.J⟩
end RightDerivedEffaceability
section P1Witness

end CohomologyConnection

namespace CohomologyConnection

/--
[p1_witness_effaceability_confirmed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean)
-/
@[path]
lemma p1_witness_effaceability_confirmed
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  ∃ N : ℤ, 0 ≤ N ∧ n ≤ N ∧ Module.finrank k (SheafCohomology.H1 k N) = 0 :=
-- proof
  (mkCechToDerivedDataP1Witness k).effaceability n

end CohomologyConnection

namespace CohomologyConnection

/--
[p1_witness_euler_confirmed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean)
-/
@[path]
lemma p1_witness_euler_confirmed
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) - (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
-- proof
  (mkCechToDerivedDataP1Witness k).euler_char n

end CohomologyConnection

/--
[CohomDeltaFunctor.idMorphism_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean)
-/
@[path]
private lemma idMorphism__eq
  {C : Type u₀}
  [Category.{v₀} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
  {n : ℕ} :
-- imply
  F.idMorphism.η n = 𝟙 (F.T n) := by
-- proof
  apply DerivedFunctorsDefs.CohomDeltaFunctor.idMorphism_ F n


-- created on 2026-10-23
