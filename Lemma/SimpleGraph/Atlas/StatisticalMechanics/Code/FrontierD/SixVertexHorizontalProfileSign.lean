import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
open Finset StatMech StatMech.FrontierD


/--
[profileAggregate_iff_signedNonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileSign.lean)
-/
@[path]
private lemma profileAggregate_iff_signedNonnegative_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalProfileAggregateDominates T sourceLeft sourceRight targetLeft targetRight ↔ SixVertexHorizontalProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.profileAggregate_iff_signedNonnegative T sourceLeft sourceRight targetLeft targetRight


-- created on 2026-10-23
