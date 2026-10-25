import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GradedRingProjDef38.Part2
open Polynomial AlgebraicGeometry Definition38


namespace Definition38

/--
[tangentCone_over_closedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedRingProjDef38.lean)
-/
@[path]
lemma tangentCone_over_closedPoint
  [CommRing R]
  {𝔪 : Ideal R} :
-- imply
  𝔪 ≤ RingHom.ker (ringHomToAssocGraded 𝔪) := by
-- proof
  intro r hr
  rw [RingHom.mem_ker]
  show (Ideal.Quotient.mk (reesIdealFromBase 𝔪)) ((algebraMap R (reesAlgebra 𝔪)) r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hr

end Definition38


-- created on 2026-10-23
