import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoOrderedStep_zeroOrUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrderedStep_zeroOrUnit_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 0 \/ sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1 \/ sixVertexDegreeTwoStrandStepSeamSign hdegree dart = -1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrderedStep_zeroOrUnit hdegree dart

/--
[sixVertexDegreeTwoOrderedAllStrands_map_sum_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrderedAllStrands_map_sum_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  ((sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).map (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrderedAllStrands_map_sum_eq_two homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoCanonicalUnitPrefix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalUnitPrefix_sum_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  ((sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle).map (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalUnitPrefix_sum homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoCanonicalUnitSuffix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalUnitSuffix_sum_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  ((sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle homegaSector hetaSector hmiddle).map (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalUnitSuffix_sum homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoCanonicalUnitPrefix_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalUnitPrefix_ne_nil_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle ≠ [] := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalUnitPrefix_ne_nil homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoCanonicalUnitSuffix_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalUnitSuffix_ne_nil_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle homegaSector hetaSector hmiddle ≠ [] := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalUnitSuffix_ne_nil homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoCanonicalUnitPrefix_append_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalUnitPrefix_append_suffix_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle ++ sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle homegaSector hetaSector hmiddle = sixVertexDegreeTwoOrderedAllStrands homega heta hdegree := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalUnitPrefix_append_suffix homega heta hdegree middle homegaSector hetaSector hmiddle


-- created on 2026-10-23
