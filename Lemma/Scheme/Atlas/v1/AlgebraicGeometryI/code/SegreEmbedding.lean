import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SegreEmbedding
open MvPolynomial


/--
[segre_relation_in_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SegreEmbedding.lean)
-/
@[path]
lemma segre_relation_in_kernel
  {k : Type*}
  [CommRing k] :
-- imply
  segreMap k (segreRelation k) = 0 := by
-- proof
  simp only [segreRelation, segreMap, map_sub, map_mul, MvPolynomial.aeval_X]
  ring

/--
[segre_algebraic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SegreEmbedding.lean)
-/
@[path]
lemma segre_algebraic_identity
  [CommRing R]
  {x₀ x₁ y₀ y₁ : R} :
-- imply
  (x₀ * y₀) * (x₁ * y₁) - (x₀ * y₁) * (x₁ * y₀) = 0 := by
-- proof
  ring


-- created on 2026-10-23
