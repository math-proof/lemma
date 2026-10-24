import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.PicardGroup
open Theorem19_14
open CurveWithOrd CurveWithConstants


namespace Theorem19_14

/--
[exact_at_functionField_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PicardGroup.lean)
-/
@[path]
lemma exact_at_functionField_mathlib
  {C : Type*}
  {k : Type*}
  {F : Type*}
  [Field k]
  [Field F] :
-- imply
  Function.Exact (constantsEmb (k := k) (F := F)) (divMap C k F) := by
-- proof
  intro f
  exact CurveWithConstants.exact_at_functionField (C := C) (k := k) f

end Theorem19_14

namespace Theorem19_14

/--
[exact_at_DivGroup_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PicardGroup.lean)
-/
@[path]
lemma exact_at_DivGroup_mathlib
  {C : Type*}
  {k : Type*}
  {F : Type*}
  [Field k]
  [Field F] :
-- imply
  Function.Exact (divMap C k F) (toPicMap C k F) := by
-- proof
  intro D
  constructor
  · intro hD
    have hD' : D ∈ (toPicMap C k F).ker := AddMonoidHom.mem_ker.mpr hD
    rw [toPicMap, QuotientAddGroup.ker_mk'] at hD'
    obtain ⟨f, hf⟩ := hD'
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    show toPicMap C k F (principalDivisor f) = 0
    have : principalDivisor f ∈ principalDivisors (C := C) (F := F) := ⟨f, rfl⟩
    have hker : principalDivisor f ∈ (toPicMap C k F).ker := by
      rwa [toPicMap, QuotientAddGroup.ker_mk']
    exact AddMonoidHom.mem_ker.mp hker

end Theorem19_14

namespace Theorem19_14

/--
[toPicMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PicardGroup.lean)
-/
@[path]
lemma toPicMap_surjective
  {C : Type*}
  {k : Type*}
  {F : Type*}
  [Field k]
  [Field F] :
-- imply
  Function.Surjective (toPicMap C k F) :=
-- proof
  QuotientAddGroup.mk'_surjective principalDivisors

end Theorem19_14

namespace Theorem19_14

/--
[picard_exact_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PicardGroup.lean)
-/
@[path]
lemma picard_exact_sequence
  {C : Type*}
  {k : Type*}
  {F : Type*}
  [Field k]
  [Field F] :
-- imply
  Function.Injective (constantsEmb (k := k) (F := F)) ∧ Function.Exact (constantsEmb (k := k) (F := F)) (divMap C k F) ∧ Function.Exact (divMap C k F) (toPicMap C k F) ∧ Function.Surjective (toPicMap C k F) :=
-- proof
  ⟨CurveWithConstants.constantsEmb_injective,
    exact_at_functionField_mathlib C k F,
    exact_at_DivGroup_mathlib C k F,
    toPicMap_surjective C k F⟩

end Theorem19_14


-- created on 2026-10-23
