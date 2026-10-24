import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronClosed
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEventuallyHasSymmetricBetheIdentification_of_densityTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronClosed.lean)
-/
@[path]
private lemma sixVertexEventuallyHasSymmetricBetheIdentification_of_densityTail_eq
  {c : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  SixVertexEventuallyHasSymmetricBetheIdentification hc := by
-- proof
  apply StatMech.FrontierD.sixVertexEventuallyHasSymmetricBetheIdentification_of_densityTail hc htail


-- created on 2026-10-23
