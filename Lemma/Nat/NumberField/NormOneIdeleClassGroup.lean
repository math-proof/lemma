import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.NormOneIdeleClassGroup
open NumberField.TopologicalIdeleGroup


/--
[normOne_mk_principalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormOneIdeleClassGroup.lean)
-/
@[path]
private lemma normOne_mk_principalEmbedding_eq
  [Field K] [NumberField K]
  {x : Kˣ} :
-- imply
  QuotientGroup.mk (s := by
-- proof
  apply NumberField.TopologicalIdeleGroup.normOne_mk_principalEmbedding K x


-- created on 2026-10-20
