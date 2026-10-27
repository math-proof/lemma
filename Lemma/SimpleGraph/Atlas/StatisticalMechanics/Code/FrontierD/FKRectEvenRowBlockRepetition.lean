import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowBlockRepetition.Part2
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectEvenRowTranslatedConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma fkRectEvenRowTranslatedConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : S}
  {shift : Nat} :
-- imply
  IsIncreasing (fkRectEvenRowTranslatedConnectionEvent R S x y shift) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslatedConnectionEvent_isIncreasing R S x y shift

/--
[fkRectCritical_evenRowTranslatedConnectionMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_evenRowTranslatedConnectionMass_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : S}
  {shift : Nat}
  {q : Real}
-- given
  (hshift : Even shift) :
-- imply
  fkRectCriticalEventMass R q (fkRectEvenRowTranslatedConnectionEvent R S x y shift) = fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_evenRowTranslatedConnectionMass R S x y shift hshift q

/--
[fkRectEvenRowBlockIntersection_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma fkRectEvenRowBlockIntersection_isIncreasing_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : S}
  {step blocks : Nat} :
-- imply
  IsIncreasing (fkRectEvenRowBlockIntersection R S x y step blocks) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowBlockIntersection_isIncreasing R S x y step blocks

/--
[fkRectCritical_evenRowBlockLower_pow_le_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_evenRowBlockLower_pow_le_intersection_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : S}
  {step blocks : Nat}
  {q a : Real}
-- given
  (hstep : Even step)
  (hq : 1 ≤ q)
  (ha : 0 ≤ a)
  (hlower : a ≤ fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y}) :
-- imply
  a ^ blocks ≤ fkRectCriticalEventMass R q (fkRectEvenRowBlockIntersection R S x y step blocks) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_evenRowBlockLower_pow_le_intersection R S x y step blocks hstep hq ha hlower

/--
[fkRectEvenRowTranslationSet_column_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma fkRectEvenRowTranslationSet_column_bounds_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {shift left right : Nat}
  {v : R.Vertex}
-- given
  (hS : ∀ v ∈ S, left ≤ v.1.val ∧ v.1.val ≤ right)
  (hv : v ∈ fkRectEvenRowTranslationSet R shift S) :
-- imply
  left ≤ v.1.val ∧ v.1.val ≤ right := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslationSet_column_bounds R S shift left right hS hv

/--
[FKRectConnectedWithin.reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hxy : FKRectConnectedWithin R omega S x y) :
-- imply
  (fkRectOpenGraph R omega).Reachable x.1 y.1 := by
-- proof
  apply StatMech.FrontierD.FKRectConnectedWithin.reachable R omega S x y hxy

/--
[fkRectEvenRowTranslatedConnection_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma fkRectEvenRowTranslatedConnection_start_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : S}
  {shift : Nat}
  {omega : R.Configuration}
-- given
  (hmem : omega ∈ fkRectEvenRowTranslatedConnectionEvent R S x y shift) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectEvenRowTranslationVertexEquiv R shift x.1) (fkRectEvenRowTranslationVertexEquiv R shift y.1) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslatedConnection_start R S x y shift omega hmem

/--
[fkRectEvenRowBlockIntersection_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowBlockRepetition.lean)
-/
@[path]
private lemma fkRectEvenRowBlockIntersection_reachable_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : S}
  {step blocks : Nat}
  {omega : R.Configuration}
-- given
  (hxy : fkRectEvenRowTranslationVertexEquiv R step x.1 = y.1)
  (hmem : omega ∈ fkRectEvenRowBlockIntersection R S x y step blocks) :
-- imply
  (fkRectOpenGraph R omega).Reachable x.1 (fkRectEvenRowTranslationVertexEquiv R (blocks * step) x.1) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowBlockIntersection_reachable R S x y step blocks hxy omega hmem


-- created on 2026-10-23
