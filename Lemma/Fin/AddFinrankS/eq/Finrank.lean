import Mathlib
import Initialize.Tactic.Attr.Basic
open Module LinearMap


/--
[dimension_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/DimensionFormula.lean)
-/
@[path]
private lemma main
  [DivisionRing F]
  [AddCommGroup V]
  [Module F V]
  [FiniteDimensional F V]
  [AddCommGroup W]
  [Module F W]
  {T : V →ₗ[F] W} :
-- imply
  finrank F (ker T) + finrank F (range T) = finrank F V := by
-- proof
  have h := T.finrank_range_add_finrank_ker
  omega


-- created on 2026-10-23
-- updated on 2026-10-26
