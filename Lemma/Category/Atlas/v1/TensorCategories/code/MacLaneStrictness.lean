import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.MacLaneStrictness.Part2
open CategoryTheory MonoidalCategory Category EGNO EGNO.MacLaneStrictness
open FreeMonoidalCategory


namespace EGNO.MacLaneStrictness

/--
[skeletal_monoidal_tensorObj_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean)
-/
@[path]
lemma skeletal_monoidal_tensorObj_assoc
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y Z : C}
-- given
  (hC : Skeletal C) :
-- imply
  (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) :=
-- proof
  hC ⟨α_ X Y Z⟩

end EGNO.MacLaneStrictness

namespace EGNO.MacLaneStrictness

/--
[skeletal_monoidal_tensorUnit_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean)
-/
@[path]
lemma skeletal_monoidal_tensorUnit_left
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X : C}
-- given
  (hC : Skeletal C) :
-- imply
  𝟙_ C ⊗ X = X :=
-- proof
  hC ⟨λ_ X⟩

end EGNO.MacLaneStrictness

namespace EGNO.MacLaneStrictness

/--
[skeletal_monoidal_tensorUnit_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean)
-/
@[path]
lemma skeletal_monoidal_tensorUnit_right
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X : C}
-- given
  (hC : Skeletal C) :
-- imply
  X ⊗ 𝟙_ C = X :=
-- proof
  hC ⟨ρ_ X⟩

end EGNO.MacLaneStrictness

namespace EGNO.MacLaneStrictness

/--
[skeleton_tensorObj_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean)
-/
@[path]
lemma skeleton_tensorObj_assoc
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X Y Z : Skeleton C} :
-- imply
  (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) :=
-- proof
  skeletal_monoidal_tensorObj_assoc (skeleton_skeletal C) X Y Z

end EGNO.MacLaneStrictness

namespace EGNO.MacLaneStrictness

/--
[skeleton_tensorUnit_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean)
-/
@[path]
lemma skeleton_tensorUnit_left
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X : Skeleton C} :
-- imply
  𝟙_ _ ⊗ X = X :=
-- proof
  skeletal_monoidal_tensorUnit_left (skeleton_skeletal C) X

end EGNO.MacLaneStrictness

namespace EGNO.MacLaneStrictness

/--
[skeleton_tensorUnit_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean)
-/
@[path]
lemma skeleton_tensorUnit_right
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {X : Skeleton C} :
-- imply
  X ⊗ 𝟙_ _ = X :=
-- proof
  skeletal_monoidal_tensorUnit_right (skeleton_skeletal C) X

end EGNO.MacLaneStrictness

namespace EGNO.MacLaneStrictness

/--
[macLane_strictness'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean)
-/
@[path]
lemma macLane_strictness'
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C] :
-- imply
  ∃ (D : Type u) (_ : Category.{v} D) (_ : MonoidalCategory D), (∀ (X Y Z : D), (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)) ∧ (∀ (X : D), 𝟙_ D ⊗ X = X) ∧ (∀ (X : D), X ⊗ 𝟙_ D = X) ∧ ∃ (e : C ≌ D), Nonempty (e.functor.Monoidal) ∧ Nonempty (e.inverse.Monoidal) :=
-- proof
  ⟨Skeleton C, inferInstance, inferInstance,
    skeleton_tensorObj_assoc C,
    skeleton_tensorUnit_left C,
    skeleton_tensorUnit_right C,
    ⟨(skeletonEquivalence C).symm, ⟨inferInstance⟩, ⟨inferInstance⟩⟩⟩
/-- Theorem 1.8.5 (MacLane Strictness): Any monoidal category is monoidally equivalent
to a strict monoidal category. -/
section MonoidalEmbedding
universe v u
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
attribute [local instance] endofunctorMonoidalCategory

end EGNO.MacLaneStrictness


-- created on 2026-10-23
