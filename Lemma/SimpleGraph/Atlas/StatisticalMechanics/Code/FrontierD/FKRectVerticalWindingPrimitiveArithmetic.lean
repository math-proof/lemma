import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingPrimitiveArithmetic
open StatMech StatMech.FrontierD


/--
[snd_dvd_of_primitive_of_not_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma snd_dvd_of_primitive_of_not_windingIndependent_eq
  {w u : Int × Int}
-- given
  (hprimitive : FKRectPrimitiveWinding w)
  (hdependent : ¬ FKRectWindingIndependent w u) :
-- imply
  w.2 ∣ u.2 := by
-- proof
  apply StatMech.FrontierD.snd_dvd_of_primitive_of_not_windingIndependent hprimitive hdependent

/--
[windingIndependent_of_primitive_of_snd_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma windingIndependent_of_primitive_of_snd_between_eq
  {w u : Int × Int}
-- given
  (hprimitive : FKRectPrimitiveWinding w)
  (hw : 0 < w.2)
  (hu0 : 0 < u.2)
  (huk : u.2 < w.2) :
-- imply
  FKRectWindingIndependent w u := by
-- proof
  apply StatMech.FrontierD.windingIndependent_of_primitive_of_snd_between hprimitive hw hu0 huk

/--
[windingIndependent_of_primitive_of_snd_between_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma windingIndependent_of_primitive_of_snd_between_neg_eq
  {w u : Int × Int}
-- given
  (hprimitive : FKRectPrimitiveWinding w)
  (hw : w.2 < 0)
  (hwu : w.2 < u.2)
  (hu0 : u.2 < 0) :
-- imply
  FKRectWindingIndependent w u := by
-- proof
  apply StatMech.FrontierD.windingIndependent_of_primitive_of_snd_between_neg hprimitive hw hwu hu0

/--
[eq_of_primitive_of_primitive_of_not_windingIndependent_of_sameSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma eq_of_primitive_of_primitive_of_not_windingIndependent_of_sameSign_eq
  {u v : Int × Int}
-- given
  (hu : FKRectPrimitiveWinding u)
  (hv : FKRectPrimitiveWinding v)
  (hdep : ¬ FKRectWindingIndependent u v)
  (hsign : 0 < u.1 * v.1 ∨ 0 < u.2 * v.2) :
-- imply
  u = v := by
-- proof
  apply StatMech.FrontierD.eq_of_primitive_of_primitive_of_not_windingIndependent_of_sameSign hu hv hdep hsign

/--
[eq_or_eq_neg_of_primitive_of_primitive_of_not_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma eq_or_eq_neg_of_primitive_of_primitive_of_not_windingIndependent_eq
  {u v : Int × Int}
-- given
  (hu : FKRectPrimitiveWinding u)
  (hv : FKRectPrimitiveWinding v)
  (hdep : ¬ FKRectWindingIndependent u v) :
-- imply
  v = u ∨ v = -u := by
-- proof
  apply StatMech.FrontierD.eq_or_eq_neg_of_primitive_of_primitive_of_not_windingIndependent hu hv hdep

/--
[primitiveWinding_split_eq_zero_or_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma primitiveWinding_split_eq_zero_or_eq_eq
  {u v w : Int × Int}
-- given
  (hu : FKRectPrimitiveWinding u)
  (hsum : u = v + w)
  (hv : v = 0 ∨ FKRectPrimitiveWinding v)
  (hw : w = 0 ∨ FKRectPrimitiveWinding w)
  (hdepv : ¬ FKRectWindingIndependent u v)
  (hdepw : ¬ FKRectWindingIndependent u w) :
-- imply
  (v = 0 ∧ w = u) ∨ (v = u ∧ w = 0) := by
-- proof
  apply StatMech.FrontierD.primitiveWinding_split_eq_zero_or_eq hu hsum hv hw hdepv hdepw

/--
[not_primitiveWinding_add_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma not_primitiveWinding_add_self_eq
  {u : Int × Int} :
-- imply
  ¬ FKRectPrimitiveWinding (u + u) := by
-- proof
  apply StatMech.FrontierD.not_primitiveWinding_add_self u

/--
[not_primitiveWinding_add_of_primitive_dependent_sameSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPrimitiveArithmetic.lean)
-/
@[path]
private lemma not_primitiveWinding_add_of_primitive_dependent_sameSign_eq
  {u v : Int × Int}
-- given
  (hu : FKRectPrimitiveWinding u)
  (hv : FKRectPrimitiveWinding v)
  (hdep : ¬ FKRectWindingIndependent u v)
  (hsign : 0 < u.1 * v.1 ∨ 0 < u.2 * v.2) :
-- imply
  ¬ FKRectPrimitiveWinding (u + v) := by
-- proof
  apply StatMech.FrontierD.not_primitiveWinding_add_of_primitive_dependent_sameSign hu hv hdep hsign


-- created on 2026-10-23
