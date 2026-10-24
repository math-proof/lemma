import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.NormOneIdeleClassGroup
open NumberField.TopologicalIdeleGroup


namespace NumberField.TopologicalIdeleGroup

/--
[normOne_mk_principalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormOneIdeleClassGroup.lean)
-/
@[path]
lemma normOne_mk_principalEmbedding
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  QuotientGroup.mk (s := by
-- proof
  rw [QuotientGroup.eq_one_iff]
  exact ⟨x, rfl⟩

end NumberField.TopologicalIdeleGroup


-- created on 2026-10-20
-- updated on 2026-10-23
