import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec23DeltaFunctorDefs.Part2
open CategoryTheory Category Limits Finset Lec23DeltaFunctorDefs


namespace Lec23DeltaFunctorDefs

/--
[SheafCohomologyData.eulerChar_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DeltaFunctorDefs.lean)
-/
@[path]
lemma SheafCohomologyData.eulerChar_add
  {data : SheafCohomologyData}
  {F' F F'' : data.CohSheaf}
-- given
  (hses : data.ShortExactSeq F' F F'') :
-- imply
  data.eulerChar F = data.eulerChar F' + data.eulerChar F'' :=
-- proof
  data.eulerChar_additive F' F F'' hses

end Lec23DeltaFunctorDefs


-- created on 2026-10-23
