import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectReflectedRowStep_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectReflectedRowStep_even_eq
  {x y : Nat} :
-- imply
  Even (fkRectReflectedRowStep x y) := by
-- proof
  apply StatMech.FrontierD.fkRectReflectedRowStep_even x y

/--
[fkRectReflectedRowStep_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectReflectedRowStep_cast_eq
  {x y : Nat} :
-- imply
  (fkRectReflectedRowStep x y : Int) = 2 * := by
-- proof
  apply StatMech.FrontierD.fkRectReflectedRowStep_cast x y

/--
[fkRectReflectedRowStep_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectReflectedRowStep_of_le_eq
  {x y : Nat}
-- given
  (hxy : x ≤ y) :
-- imply
  fkRectReflectedRowStep x y = 2 * (y - x) := by
-- proof
  apply StatMech.FrontierD.fkRectReflectedRowStep_of_le hxy

/--
[fkRectReflectedRowStep_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectReflectedRowStep_of_ge_eq
  {x y : Nat}
-- given
  (hyx : y ≤ x) :
-- imply
  fkRectReflectedRowStep x y = 2 * (x - y) := by
-- proof
  apply StatMech.FrontierD.fkRectReflectedRowStep_of_ge hyx

/--
[fkRectReflectedRowStep_pos_of_span](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectReflectedRowStep_pos_of_span_eq
  {n x y : Nat}
-- given
  (hspan : (n : Int) ≤ 2 * |(y : Int) - x| + 2) :
-- imply
  0 < fkRectReflectedRowStep x y ∨ n ≤ 2 := by
-- proof
  apply StatMech.FrontierD.fkRectReflectedRowStep_pos_of_span n x y hspan

/--
[fkRectRowTranslate_eq_add_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectRowTranslate_eq_add_of_lt_eq
  {R : FKRectTorus}
  {offset : Nat}
  {y : Fin R.height}
-- given
  (hlt : y.val + offset < R.height) :
-- imply
  fkRectRowTranslate R offset y = ⟨y.val + offset, hlt⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_eq_add_of_lt R offset y hlt

/--
[fkRectRowTranslate_reflection_eq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectRowTranslate_reflection_eq_sub_eq
  {R : FKRectTorus}
  {offset center : Nat}
  {y : Fin R.height}
-- given
  (hle : y.val ≤ offset + 2 * center)
  (hlt : offset + 2 * center - y.val < R.height) :
-- imply
  fkRectRowTranslate R offset (fkRectRowReflection R center y) = ⟨offset + 2 * center - y.val, hlt⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_reflection_eq_sub R offset center y hle hlt

/--
[fkRectEvenRowTranslation_reflection_of_row_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectEvenRowTranslation_reflection_of_row_le_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hxy : x.2.val ≤ y.2.val) :
-- imply
  fkRectEvenRowTranslationVertexEquiv R (fkRectReflectedRowStep x.2.val y.2.val) x = fkRectDevelopedReflectionVertexEquiv R y.2.val x := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslation_reflection_of_row_le R x y hxy

/--
[fkRectEvenRowTranslation_reflection_of_row_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectEvenRowTranslation_reflection_of_row_ge_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hyx : y.2.val ≤ x.2.val) :
-- imply
  fkRectEvenRowTranslationVertexEquiv R (fkRectReflectedRowStep x.2.val y.2.val) (fkRectDevelopedReflectionVertexEquiv R y.2.val x) = x := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslation_reflection_of_row_ge R x y hyx

/--
[FKRectOrientedEvenRowBlock.translate_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma translate_carrier_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectOrientedEvenRowBlock R q scale}
  {offset : Nat}
-- given
  (hoffset : Even offset) :
-- imply
  (B.translate offset hoffset).carrier = fkRectEvenRowTranslationSet R offset B.carrier := by
-- proof
  apply StatMech.FrontierD.FKRectOrientedEvenRowBlock.translate_carrier B offset hoffset

/--
[FKRectOrientedEvenRowBlock.translate_massFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma translate_massFloor_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectOrientedEvenRowBlock R q scale}
  {offset : Nat}
-- given
  (hoffset : Even offset) :
-- imply
  (B.translate offset hoffset).massFloor = B.massFloor := by
-- proof
  apply StatMech.FrontierD.FKRectOrientedEvenRowBlock.translate_massFloor B offset hoffset

/--
[fkRectOrientedEvenRowBlockOfReflectedCarrier_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectOrientedEvenRowBlockOfReflectedCarrier_carrier_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {S : Set R.Vertex}
  {x y : S}
  {massFloor : Real}
-- given
  (hspan : (scale : Int) ≤ 2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
  (hrows : x.1.2.val ≤ 8 * scale + 1 ∧ y.1.2.val ≤ 8 * scale + 1)
  (hmassFloor : 0 ≤ massFloor)
  (hlower : massFloor ≤ fkRectCriticalEventMass R q (fkRectReflectedCarrierConnectionEvent R S x y))
  (hcolumns : ∀ v ∈ S ∪ fkRectDevelopedReflectionSet R y.1.2.val S, v.1.val ≤ 4 * scale) :
-- imply
  (fkRectOrientedEvenRowBlockOfReflectedCarrier R q scale S x y hspan hrows hmassFloor hlower hcolumns).carrier = S ∪ fkRectDevelopedReflectionSet R y.1.2.val S := by
-- proof
  apply StatMech.FrontierD.fkRectOrientedEvenRowBlockOfReflectedCarrier_carrier R q scale S x y hspan hrows hmassFloor hlower hcolumns

/--
[fkRectOrientedEvenRowBlockOfReflectedCarrier_massFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectOrientedEvenRowBlockOfReflectedCarrier_massFloor_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {S : Set R.Vertex}
  {x y : S}
  {massFloor : Real}
-- given
  (hspan : (scale : Int) ≤ 2 * |(y.1.2.val : Int) - x.1.2.val| + 2)
  (hrows : x.1.2.val ≤ 8 * scale + 1 ∧ y.1.2.val ≤ 8 * scale + 1)
  (hmassFloor : 0 ≤ massFloor)
  (hlower : massFloor ≤ fkRectCriticalEventMass R q (fkRectReflectedCarrierConnectionEvent R S x y))
  (hcolumns : ∀ v ∈ S ∪ fkRectDevelopedReflectionSet R y.1.2.val S, v.1.val ≤ 4 * scale) :
-- imply
  (fkRectOrientedEvenRowBlockOfReflectedCarrier R q scale S x y hspan hrows hmassFloor hlower hcolumns).massFloor = massFloor := by
-- proof
  apply StatMech.FrontierD.fkRectOrientedEvenRowBlockOfReflectedCarrier_massFloor R q scale S x y hspan hrows hmassFloor hlower hcolumns

/--
[fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {v : (fkRectQuarterTurnTorus R hH).Vertex}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hH : 4 < R.height)
  (hv : v ∈ fkRectQuarterTurnSet R hH (fkRectDevelopedThreeByOneTorusCarrier R n)) :
-- imply
  v.2.val ≤ 8 * n + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurn_developedThreeByOneCarrier_row_bounds R n hn hwidth hheight hH hv

/--
[fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {center : Nat}
  {v : R.Vertex}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 12 * n + 2 < R.height)
  (hcenter : center ≤ 4 * n)
  (hv : v ∈ fkRectEvenRowTranslationSet R (4 * n + 2) (fkRectDevelopedThreeByOneTorusCarrier R n ∪ fkRectDevelopedReflectionSet R center (fkRectDevelopedThreeByOneTorusCarrier R n))) :
-- imply
  1 ≤ v.2.val ∧ v.2.val ≤ 12 * n + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_reflectedUnion_evenOffset_row_bounds R n hwidth hheight center hcenter hv

/--
[fkRectQuarterTurn_reflectedUnion_evenOffset_row_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectQuarterTurn_reflectedUnion_evenOffset_row_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {center : Nat}
  {v : (fkRectQuarterTurnTorus R hH).Vertex}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hH : 4 < R.height)
  (hrotHeight : 24 * n + 4 < (fkRectQuarterTurnTorus R hH).height)
  (hcenter : center ≤ 8 * n + 1)
  (hv : v ∈ fkRectEvenRowTranslationSet (fkRectQuarterTurnTorus R hH) (8 * n + 2) (fkRectQuarterTurnSet R hH (fkRectDevelopedThreeByOneTorusCarrier R n) ∪ fkRectDevelopedReflectionSet (fkRectQuarterTurnTorus R hH) center (fkRectQuarterTurnSet R hH (fkRectDevelopedThreeByOneTorusCarrier R n)))) :
-- imply
  1 ≤ v.2.val ∧ v.2.val ≤ 24 * n + 4 := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurn_reflectedUnion_evenOffset_row_bounds R n hn hwidth hheight hH hrotHeight center hcenter hv

/--
[fkRectCritical_developedThreeByOne_exists_orientedEvenRowBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_orientedEvenRowBlock_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  let hH : 4 < R.height := by omega Nonempty (FKRectOrientedEvenRowBlock R q n) ∨ Nonempty (FKRectOrientedEvenRowBlock (fkRectQuarterTurnTorus R hH) q n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_orientedEvenRowBlock R n hn hwidth hheight hq

/--
[fkRectCritical_developedThreeByOne_exists_positiveRowOrientedBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectOrientedEvenRowBlock.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_positiveRowOrientedBlock_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 12 * n + 2 < R.width)
  (hheight : 12 * n + 2 < R.height)
  (hq : 1 ≤ q) :
-- imply
  let hH : 4 < R.height := by omega Nonempty (FKRectPositiveRowOrientedBlock R q n) ∨ Nonempty (FKRectPositiveRowOrientedBlock (fkRectQuarterTurnTorus R hH) q n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_positiveRowOrientedBlock R n hn hwidth hheight hq


-- created on 2026-10-23
