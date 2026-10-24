import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedInactive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer dart.1.1 = false := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hinactive

/--
[sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart_of_unmasked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedInactive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart_of_unmasked_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hmaskD : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer dart.1.1 = false)
  (hnext : Not (activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart))) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart = alignedBoundaryPerm homega heta hdegree false dart := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart_of_unmasked homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hmaskD hnext

/--
[sixVertexDegreeTwoCanonicalExpanded_falseDart_color_of_unmasked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedInactive.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpanded_falseDart_color_of_unmasked_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hmaskD : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer dart.1.1 = false)
  (hnext : Not (activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart))) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpanded_falseDart_color_of_unmasked homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hmaskD hnext


-- created on 2026-10-23
