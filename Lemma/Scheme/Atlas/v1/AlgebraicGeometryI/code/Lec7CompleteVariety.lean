import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec7CompleteVariety
open AlgebraicGeometry CategoryTheory Limits Formalization Formalization.Lec7CompleteVariety


namespace Formalization.Lec7CompleteVariety

/--
[isProper_of_isCompleteVariety](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7CompleteVariety.lean)
-/
@[path]
lemma isProper_of_isCompleteVariety
  {X S : Scheme.{u}}
  {f : X ⟶ S}
  [hc : IsCompleteVariety f]
  [LocallyOfFiniteType f] :
-- imply
  IsProper f where toIsSeparated :=
-- proof
  hc.isSeparated
    toUniversallyClosed := hc.universallyClosed

end Formalization.Lec7CompleteVariety


-- created on 2026-10-23
