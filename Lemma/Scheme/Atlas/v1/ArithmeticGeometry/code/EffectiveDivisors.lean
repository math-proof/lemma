import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
open CurveDivisor


namespace CurveDivisor

/--
[isEffective_iff_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean)
-/
@[path]
lemma isEffective_iff_nonneg
  {D : CurveDivisor C} :
-- imply
  D.IsEffective ↔ 0 ≤ D := by
-- proof
  rw [IsEffective, Finsupp.le_def]
  simp

end CurveDivisor

namespace CurveDivisor

/--
[le_iff_isEffective_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean)
-/
@[path]
lemma le_iff_isEffective_sub
  {D₁ D₂ : CurveDivisor C} :
-- imply
  D₁ ≤ D₂ ↔ (D₂ - D₁).IsEffective := by
-- proof
  rw [isEffective_iff_nonneg, sub_nonneg]

end CurveDivisor

namespace CurveDivisor

/--
[IsEffective.add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean)
-/
@[path]
lemma IsEffective.add
  {D₁ D₂ : CurveDivisor C}
-- given
  (h₁ : D₁.IsEffective)
  (h₂ : D₂.IsEffective) :
-- imply
  (D₁ + D₂).IsEffective := by
-- proof
  intro P
  simp only [Finsupp.coe_add, Pi.add_apply]
  linarith [h₁ P, h₂ P]

end CurveDivisor

namespace CurveDivisor

/--
[positivePart_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean)
-/
@[path]
lemma positivePart_apply
  {D : CurveDivisor C}
  {P : C} :
-- imply
  D.positivePart P = max (D P) 0 := by
-- proof
  simp [positivePart, Finsupp.mapRange_apply]

end CurveDivisor

namespace CurveDivisor

/--
[negativePart_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean)
-/
@[path]
lemma negativePart_apply
  {D : CurveDivisor C}
  {P : C} :
-- imply
  D.negativePart P = max (-(D P)) 0 := by
-- proof
  simp [negativePart, Finsupp.mapRange_apply]

end CurveDivisor

namespace CurveDivisor

/--
[positivePart_isEffective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean)
-/
@[path]
lemma positivePart_isEffective
  {D : CurveDivisor C} :
-- imply
  D.positivePart.IsEffective := by
-- proof
  intro P
  simp

end CurveDivisor

namespace CurveDivisor

/--
[decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EffectiveDivisors.lean)
-/
@[path]
lemma decomposition
  {D : CurveDivisor C} :
-- imply
  D = D.positivePart - D.negativePart := by
-- proof
  ext P
  simp only [positivePart_apply, negativePart_apply, Finsupp.coe_sub, Pi.sub_apply]
  omega

end CurveDivisor


-- created on 2026-10-23
