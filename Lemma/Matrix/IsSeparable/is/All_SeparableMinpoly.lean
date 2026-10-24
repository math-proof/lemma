import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraNotes.code.FieldExtensionsGaloisRemaining
open FieldExtensionsGalois


namespace FieldExtensionsGalois

/--
[isSeparable_iff_minpoly_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/FieldExtensionsGaloisRemaining.lean)
-/
@[path]
lemma isSeparable_iff_minpoly_separable
  {F E : Type*}
  [Field F]
  [Field E]
  [Algebra F E]
  [Algebra.IsAlgebraic F E] :
-- imply
  Algebra.IsSeparable F E ↔ ∀ α : E, (minpoly F α).Separable := by
-- proof
  constructor
  · intro h α; exact Algebra.IsSeparable.isSeparable F α
  · intro h; exact ⟨fun α => h α⟩

end FieldExtensionsGalois


-- created on 2026-10-23
