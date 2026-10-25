import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
open SimpleGraph StatMech StatMech.FrontierD


/--
[FKRectConnectedWithin.mono_configuration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma mono_configuration_eq
  {R : FKRectTorus}
  {omega tau : R.Configuration}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hopen : omega ≤ tau)
  (hxy : FKRectConnectedWithin R omega S x y) :
-- imply
  FKRectConnectedWithin R tau S x y := by
-- proof
  apply StatMech.FrontierD.FKRectConnectedWithin.mono_configuration R hopen S hxy

/--
[fkRectConnectedWithin_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma fkRectConnectedWithin_isIncreasing_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : S} :
-- imply
  IsIncreasing {omega : R.Configuration | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedWithin_isIncreasing R S x y

/--
[FKRectConnectedWithin.mono_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma mono_set_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {S T : Set R.Vertex}
  {x y : S}
-- given
  (hST : S ⊆ T)
  (hxy : FKRectConnectedWithin R omega S x y) :
-- imply
  FKRectConnectedWithin R omega T ⟨x, hST x.2⟩ ⟨y, hST y.2⟩ := by
-- proof
  apply StatMech.FrontierD.FKRectConnectedWithin.mono_set R omega hST hxy

/--
[FKRectConnectedWithin.trans_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma trans_union_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {S T : Set R.Vertex}
  {x y z : R.Vertex}
-- given
  (hx : x ∈ S)
  (hyS : y ∈ S)
  (hyT : y ∈ T)
  (hz : z ∈ T)
  (hxy : FKRectConnectedWithin R omega S ⟨x, hx⟩ ⟨y, hyS⟩)
  (hyz : FKRectConnectedWithin R omega T ⟨y, hyT⟩ ⟨z, hz⟩) :
-- imply
  FKRectConnectedWithin R omega (S ∪ T) ⟨x, Or.inl hx⟩ ⟨z, Or.inr hz⟩ := by
-- proof
  apply StatMech.FrontierD.FKRectConnectedWithin.trans_union R omega hx hyS hyT hz hxy hyz

/--
[fkRectVerticalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma fkRectVerticalCrossingEvent_isIncreasing_eq
  {R : FKRectTorus}
  {x0 x1 y0 y1 : Nat} :
-- imply
  IsIncreasing (fkRectVerticalCrossingEvent R x0 x1 y0 y1) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCrossingEvent_isIncreasing R x0 x1 y0 y1

/--
[fkRectHorizontalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma fkRectHorizontalCrossingEvent_isIncreasing_eq
  {R : FKRectTorus}
  {x0 x1 y0 y1 : Nat} :
-- imply
  IsIncreasing (fkRectHorizontalCrossingEvent R x0 x1 y0 y1) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCrossingEvent_isIncreasing R x0 x1 y0 y1

/--
[fkRectVerticalCrossingEvent_eq_finiteEndpointUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma fkRectVerticalCrossingEvent_eq_finiteEndpointUnion_eq
  {R : FKRectTorus}
  {x0 x1 y0 y1 : Nat} :
-- imply
  fkRectVerticalCrossingEvent R x0 x1 y0 y1 = fkRectFiniteEventUnion (fkRectVerticalEndpointPairs R x0 x1 y0 y1) (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCrossingEvent_eq_finiteEndpointUnion R x0 x1 y0 y1

/--
[fkRectVerticalEndpointPairs_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma fkRectVerticalEndpointPairs_nonempty_eq
  {R : FKRectTorus}
  {x0 x1 y0 y1 : Nat}
-- given
  (hxx : x0 ≤ x1)
  (hx1 : x1 < R.width)
  (hyy : y0 ≤ y1)
  (hy1 : y1 < R.height) :
-- imply
  (fkRectVerticalEndpointPairs R x0 x1 y0 y1).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalEndpointPairs_nonempty R x0 x1 y0 y1 hxx hx1 hyy hy1

/--
[exists_verticalEndpoint_eventMass_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean)
-/
@[path]
private lemma exists_verticalEndpoint_eventMass_ge_eq
  {R : FKRectTorus}
  {q c : Real}
  {x0 x1 y0 y1 : Nat}
-- given
  (hq : 0 < q)
  (hxx : x0 ≤ x1)
  (hx1 : x1 < R.width)
  (hyy : y0 ≤ y1)
  (hy1 : y1 < R.height)
  (hc : c ≤ fkRectCriticalEventMass R q (fkRectVerticalCrossingEvent R x0 x1 y0 y1)) :
-- imply
  ∃ p ∈ fkRectVerticalEndpointPairs R x0 x1 y0 y1, c ≤ ((fkRectVerticalEndpointPairs R x0 x1 y0 y1).card : Real) * fkRectCriticalEventMass R q (fkRectVerticalEndpointConnectionEvent R x0 x1 y0 y1 p) := by
-- proof
  apply StatMech.FrontierD.exists_verticalEndpoint_eventMass_ge R hq x0 x1 y0 y1 hxx hx1 hyy hy1 hc


-- created on 2026-10-23
