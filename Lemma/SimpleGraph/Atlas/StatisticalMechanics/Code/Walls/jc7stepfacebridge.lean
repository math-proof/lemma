import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc7stepfacebridge
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc7_dartFace_iterate_mem_olb_orbitLoop_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7stepfacebridge.lean)
-/
@[path]
private lemma jc7_dartFace_iterate_mem_olb_orbitLoop_support_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  dartFace ((dartNext K)^[n] e) ∈ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Walls.jc7_dartFace_iterate_mem_olb_orbitLoop_support K hK e he n


-- created on 2026-10-23
