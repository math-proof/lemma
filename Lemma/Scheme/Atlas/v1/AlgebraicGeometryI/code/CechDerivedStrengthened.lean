import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CechDerivedStrengthened
open CategoryTheory CategoryTheory.Limits DerivedFunctorsDefs CechDerivedComparison CechDerivedIsomorphismProof
open DerivedFunctorsDefs
open DerivedFunctorsDefs CohomologyConnection


namespace DerivedFunctorsDefs

variable {C : Type u} [Category.{v} C] [Abelian C] [Category D] [Abelian D]
/--
[compMorphism_η](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
components. -/
@[simp]
lemma CohomDeltaFunctor.compMorphism_η {F G H : CohomDeltaFunctor C D}
  (m₁ : F.Morphism G) (m₂ : G.Morphism H) (n : ℕ) :
  (CohomDeltaFunctor.compMorphism m₁ m₂).η n = m₁.η n ≫ m₂.η n :=
  rfl
end DerivedFunctorsDefs
namespace DerivedFunctorsDefs
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type*} [Category D] [Abelian D]
end DerivedFunctorsDefs
namespace CechDerivedComparison
universe v₂ u₂
variable {C : Type u₂} [Category.{v₂} C] [Abelian C]
  {D : Type*} [Category D] [Abelian D]
open DerivedFunctorsDefs


namespace CechDerivedComparison

/--
[roundtrip_eq_id_of_effaceable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma roundtrip_eq_id_of_effaceable
  {C : Type u₂}
  [Category.{v₂} C]
  [Abelian C]
  {F : CohomDeltaFunctor C D}
  {m : F.Morphism F}
-- given
  (hF : F.IsEffaceable)
  (h₀ : m.η 0 = 𝟙 (F.T 0)) :
-- imply
  ∀ n, m.η n = 𝟙 (F.T n) := by
-- proof
  have := effaceable_morphism_unique F F hF m F.idMorphism
    (by rw [h₀]; rfl)
  intro n
  rw [this n]
  rfl
end CechDerivedComparison
namespace CechDerivedIsomorphismProof
universe v₃ u₃
variable {C : Type u₃} [Category.{v₃} C] [Abelian C]
  {D : Type*} [Category D] [Abelian D]
open DerivedFunctorsDefs CohomologyConnection

end CechDerivedComparison

namespace CechDerivedIsomorphismProof

/--
[CechDerivedComparisonData.forward_backward_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma CechDerivedComparisonData.forward_backward_eq_id
  {C : Type u₃}
  [Category.{v₃} C]
  [Abelian C]
  {n : ℕ}
-- given
  (data : CechDerivedComparisonData (C := C) (D := D)) :
-- imply
  data.forward.η n ≫ data.backward.η n = 𝟙 (data.cech.T n) := by
-- proof
  let comp := CohomDeltaFunctor.compMorphism data.forward data.backward
  have h₀ : comp.η 0 = 𝟙 (data.cech.T 0) := data.forward_backward_zero
  have := CechDerivedComparison.roundtrip_eq_id_of_effaceable
    data.cech data.cech_effaceable comp h₀
  exact this n

end CechDerivedIsomorphismProof

namespace CechDerivedIsomorphismProof

/--
[CechDerivedComparisonData.backward_forward_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma CechDerivedComparisonData.backward_forward_eq_id
  {C : Type u₃}
  [Category.{v₃} C]
  [Abelian C]
  {n : ℕ}
-- given
  (data : CechDerivedComparisonData (C := C) (D := D)) :
-- imply
  data.backward.η n ≫ data.forward.η n = 𝟙 (data.derived.T n) := by
-- proof
  let comp := CohomDeltaFunctor.compMorphism data.backward data.forward
  have h₀ : comp.η 0 = 𝟙 (data.derived.T 0) := data.backward_forward_zero
  have := CechDerivedComparison.roundtrip_eq_id_of_effaceable
    data.derived data.derived_effaceable comp h₀
  exact this n

end CechDerivedIsomorphismProof

namespace CechDerivedIsomorphismProof

/--
[CechDerivedComparisonData.forward_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma CechDerivedComparisonData.forward_isIso
  {C : Type u₃}
  [Category.{v₃} C]
  [Abelian C]
  {n : ℕ}
-- given
  (data : CechDerivedComparisonData (C := C) (D := D)) :
-- imply
  IsIso (data.forward.η n) := by
-- proof
  refine ⟨⟨data.backward.η n, ?_, ?_⟩⟩
  ·
    have h := data.forward_backward_eq_id n
    exact h
  ·
    exact data.backward_forward_eq_id n

end CechDerivedIsomorphismProof

namespace CechDerivedIsomorphismProof

/--
[CechDerivedComparisonData.backward_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma CechDerivedComparisonData.backward_isIso
  {C : Type u₃}
  [Category.{v₃} C]
  [Abelian C]
  {n : ℕ}
-- given
  (data : CechDerivedComparisonData (C := C) (D := D)) :
-- imply
  IsIso (data.backward.η n) := by
-- proof
  refine ⟨⟨data.forward.η n, ?_, ?_⟩⟩
  · exact data.backward_forward_eq_id n
  · exact data.forward_backward_eq_id n

end CechDerivedIsomorphismProof

namespace CechDerivedIsomorphismProof

/--
[CechDerivedComparisonData.comparison_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma CechDerivedComparisonData.comparison_unique
  {C : Type u₃}
  [Category.{v₃} C]
  [Abelian C]
  {m : data.cech.Morphism data.derived}
-- given
  (data : CechDerivedComparisonData (C := C) (D := D))
  (h₀ : m.η 0 = data.forward.η 0) :
-- imply
  ∀ n, m.η n = data.forward.η n :=
-- proof
  effaceable_morphism_unique data.cech data.derived data.cech_effaceable
    m data.forward h₀

end CechDerivedIsomorphismProof

namespace CechDerivedIsomorphismProof

/--
[CechDerivedComparisonData.inverse_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma CechDerivedComparisonData.inverse_unique
  {C : Type u₃}
  [Category.{v₃} C]
  [Abelian C]
  {m : data.derived.Morphism data.cech}
-- given
  (data : CechDerivedComparisonData (C := C) (D := D))
  (h₀ : m.η 0 = data.backward.η 0) :
-- imply
  ∀ n, m.η n = data.backward.η n :=
-- proof
  effaceable_morphism_unique data.derived data.cech data.derived_effaceable
    m data.backward h₀

end CechDerivedIsomorphismProof

namespace CechDerivedIsomorphismProof

/--
[CechDerivedFullComparison.forward_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
lemma CechDerivedFullComparison.forward_isIso
  {C : Type u₃}
  [Category.{v₃} C]
  [Abelian C]
  {n : ℕ}
-- given
  (data : CechDerivedComparisonData (C := C) (D := D))
  (comp : CechDerivedFullComparison (C := C) (D := D)) :
-- imply
  IsIso (comp.forward.η n) :=
-- proof
  comp.toComparisonData.forward_isIso n

end CechDerivedIsomorphismProof

/--
[CohomDeltaFunctor.compMorphism_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedStrengthened.lean)
-/
@[path]
private lemma compMorphism__eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {F G H : CohomDeltaFunctor C D}
  {m₁ : F.Morphism G}
  {m₂ : G.Morphism H}
  {n : ℕ} :
-- imply
  (CohomDeltaFunctor.compMorphism m₁ m₂).η n = m₁.η n ≫ m₂.η n := by
-- proof
  apply DerivedFunctorsDefs.CohomDeltaFunctor.compMorphism_ m₁ m₂ n


-- created on 2026-10-23
