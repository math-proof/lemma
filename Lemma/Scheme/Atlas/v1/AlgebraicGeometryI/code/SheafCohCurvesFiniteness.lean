import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
open SheafCohCurvesFiniteness
open CohomologyP1 SheafCohomology


namespace SheafCohCurvesFiniteness

/--
[cech2_higher_vanishing_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohCurvesFiniteness.lean)
-/
@[path]
lemma cech2_higher_vanishing_finrank
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank k (PUnit ⧸ (⊤ : Submodule k PUnit)) = 0 := by
-- proof
  haveI : Subsingleton (PUnit ⧸ (⊤ : Submodule k PUnit)) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

end SheafCohCurvesFiniteness


-- created on 2026-10-23
