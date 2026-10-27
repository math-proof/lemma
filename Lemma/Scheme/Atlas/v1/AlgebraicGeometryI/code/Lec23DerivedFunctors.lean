import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors.Part3
open CategoryTheory Category Limits Lec23


namespace Lec23

/--
[rightDerived_vanishes_on_injectives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean)
-/
@[path]
lemma rightDerived_vanishes_on_injectives
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {n : ℕ}
  {X : C}
  [Injective X] :
-- imply
  IsZero ((F.rightDerived (n + 1)).obj X) :=
-- proof
  Functor.isZero_rightDerived_obj_injective_succ F n X

end Lec23

namespace Lec23

/--
[rightDerived_effaceable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean)
-/
@[path]
lemma rightDerived_effaceable
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [EnoughInjectives C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {n : ℕ}
  {M : C}
-- given
  (hn : 0 < n) :
-- imply
  ∃ (I : C) (φ : M ⟶ I), Mono φ ∧ IsZero ((F.rightDerived n).obj I) := by
-- proof
  obtain ⟨⟨J, _, f, _⟩⟩ := (inferInstance : EnoughInjectives C).presentation M
  refine ⟨J, f, ‹_›, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact Functor.isZero_rightDerived_obj_injective_succ F k J

end Lec23

namespace Lec23

/--
[prop42_exactness_at_X1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean)
-/
@[path]
lemma prop42_exactness_at_X1
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (ShortComplex.mk (hS.δ i j hij) (HomologicalComplex.homologyMap S.f j) (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact :=
-- proof
  hS.homology_exact₁ i j hij

end Lec23

namespace Lec23

/--
[prop42_exactness_at_X2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean)
-/
@[path]
lemma prop42_exactness_at_X2
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  {i : ι}
-- given
  (hS : S.ShortExact) :
-- imply
  (ShortComplex.mk (HomologicalComplex.homologyMap S.f i) (HomologicalComplex.homologyMap S.g i) (by rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])).Exact :=
-- proof
  hS.homology_exact₂ i

end Lec23

namespace Lec23

/--
[prop42_exactness_at_X3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean)
-/
@[path]
lemma prop42_exactness_at_X3
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (ShortComplex.mk (HomologicalComplex.homologyMap S.g i) (hS.δ i j hij) (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
-- proof
  hS.homology_exact₃ i j hij

end Lec23

namespace Lec23

/--
[injective_isAdjustedToFunctor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean)
-/
@[path]
lemma injective_isAdjustedToFunctor
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {M : C}
  [Injective M] :
-- imply
  IsAdjustedToFunctor F M := by
-- proof
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact Functor.isZero_rightDerived_obj_injective_succ F k M

end Lec23

namespace Lec23

/--
[injRes_objects_adjusted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean)
-/
@[path]
lemma injRes_objects_adjusted
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasInjectiveResolutions C]
  [Category D]
  [Abelian D]
  {F : C ⥤ D}
  [F.Additive]
  {M : C}
  {I : InjectiveResolution M}
  {n : ℕ} :
-- imply
  IsAdjustedToFunctor F (I.cocomplex.X n) :=
-- proof
  injective_isAdjustedToFunctor F (I.cocomplex.X n)

end Lec23


-- created on 2026-10-23
