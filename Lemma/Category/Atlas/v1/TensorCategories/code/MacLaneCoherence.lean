import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.MacLaneCoherence
open CategoryTheory MonoidalCategory Category EGNO EGNO.MacLaneCoherence


namespace EGNO.MacLaneCoherence

/--
[macLane_coherence_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneCoherence.lean)
-/
@[path]
lemma macLane_coherence_free
  {C : Type*} :
-- imply
  Quiver.IsThin (FreeMonoidalCategory C) :=
-- proof
  FreeMonoidalCategory.subsingleton_hom

end EGNO.MacLaneCoherence

/--
[Theorem_1_9_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneCoherence.lean)
-/
@[path]
private lemma Theorem_1_9_1_eq
  [Category D]
  [MonoidalCategory D]
  {f : C → D}
  {P₁ P₂ : FreeMonoidalCategory C}
  {g₁ g₂ : P₁ ⟶ P₂} :
-- imply
  (FreeMonoidalCategory.project f).map g₁ = (FreeMonoidalCategory.project f).map g₂ := by
-- proof
  apply EGNO.MacLaneCoherence.Theorem_1_9_1 f g₁ g₂


-- created on 2026-10-23
