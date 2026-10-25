import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.ClosedPointMorphism
open MulAction ClosedPoint


/--
[orbitRel_map_of_equivariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ClosedPointMorphism.lean)
-/
@[path]
private lemma orbitRel_map_of_equivariant_eq
  [Group G]
  [MulAction G C₁]
  [MulAction G C₂]
  {φ : C₁ → C₂}
  ⦃a b : C₁⦄
-- given
  (hφ : ∀ (g : G) (P : C₁), φ (g • P) = g • φ P)
  (hab : (orbitRel G C₁).r a b) :
-- imply
  (orbitRel G C₂).r (φ a) (φ b) := by
-- proof
  apply ClosedPoint.orbitRel_map_of_equivariant φ hφ hab


-- created on 2026-10-23
