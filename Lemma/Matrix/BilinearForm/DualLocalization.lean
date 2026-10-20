import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.BilinearForm.DualLocalization
open LinearMap
open BilinForm


/--
[dualSubmodule_span_localization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearForm/DualLocalization.lean)
-/
@[path]
private lemma dualSubmodule_span_localization_eq
  [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  {B : LinearMap.BilinForm K V}
  {S : Submonoid A}
  {M : Submodule A V}
-- given
  (hS : S ≤ nonZeroDivisors A)
  (hM : M.FG) :
-- imply
  let Aₛ := by
-- proof
  apply LinearMap.BilinForm.dualSubmodule_span_localization B S hS M hM


-- created on 2026-10-20
