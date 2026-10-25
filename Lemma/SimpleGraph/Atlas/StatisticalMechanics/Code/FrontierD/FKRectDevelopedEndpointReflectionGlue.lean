import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointReflectionGlue.Part3
open Set StatMech StatMech.FrontierD


/--
[fkRectRowReflection_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectRowReflection_center_eq
  {R : FKRectTorus}
  {y : Fin R.height} :
-- imply
  fkRectRowReflection R y.val y = y := by
-- proof
  apply StatMech.FrontierD.fkRectRowReflection_center R y

/--
[fkRectDevelopedReflectionVertexEquiv_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionVertexEquiv_center_eq
  {R : FKRectTorus}
  {v : R.Vertex} :
-- imply
  fkRectDevelopedReflectionVertexEquiv R v.2.val v = v := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionVertexEquiv_center R v

/--
[fkRectOpenGraph_developedReflection_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectOpenGraph_developedReflection_reachable_iff_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration}
  {x y : R.Vertex} :
-- imply
  (fkRectOpenGraph R (fkRectDevelopedReflectionConfigurationEquiv R center omega)).Reachable (fkRectDevelopedReflectionVertexEquiv R center x) (fkRectDevelopedReflectionVertexEquiv R center y) ↔ (fkRectOpenGraph R omega).Reachable x y := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_developedReflection_reachable_iff R center omega x y

/--
[fkRectDevelopedReflection_mem_connectionEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedReflection_mem_connectionEvent_iff_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration}
  {x y : R.Vertex} :
-- imply
  fkRectDevelopedReflectionConfigurationEquiv R center omega ∈ fkRectTorusConnectionEvent R (fkRectDevelopedReflectionVertexEquiv R center x) (fkRectDevelopedReflectionVertexEquiv R center y) ↔ omega ∈ fkRectTorusConnectionEvent R x y := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflection_mem_connectionEvent_iff R center omega x y

/--
[fkRectCritical_connectionMass_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectCritical_connectionMass_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {q : Real}
  {x y : R.Vertex} :
-- imply
  fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R (fkRectDevelopedReflectionVertexEquiv R center x) (fkRectDevelopedReflectionVertexEquiv R center y)) = fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x y) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectionMass_developedReflection R center q x y

/--
[fkRectConnectedWithin_developedReflection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectConnectedWithin_developedReflection_iff_eq
  {R : FKRectTorus}
  {center : Nat}
  {omega : R.Configuration}
  {S : Set R.Vertex}
  {x y : S} :
-- imply
  FKRectConnectedWithin R (fkRectDevelopedReflectionConfigurationEquiv R center omega) (fkRectDevelopedReflectionSet R center S) (fkRectDevelopedReflectionSetEquiv R center S x) (fkRectDevelopedReflectionSetEquiv R center S y) ↔ FKRectConnectedWithin R omega S x y := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedWithin_developedReflection_iff R center omega S x y

/--
[fkRectCritical_connectedWithinMass_developedReflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectCritical_connectedWithinMass_developedReflection_eq
  {R : FKRectTorus}
  {center : Nat}
  {q : Real}
  {S : Set R.Vertex}
  {x y : S} :
-- imply
  fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega (fkRectDevelopedReflectionSet R center S) (fkRectDevelopedReflectionSetEquiv R center S x) (fkRectDevelopedReflectionSetEquiv R center S y)} = fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectedWithinMass_developedReflection R center q S x y

/--
[fkRectCritical_connectedWithinMass_sq_le_reflectedUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectCritical_connectedWithinMass_sq_le_reflectedUnion_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hq : 1 ≤ q) :
-- imply
  let center := y.1.2.val let Sr := fkRectDevelopedReflectionSet R center S let xr := fkRectDevelopedReflectionVertexEquiv R center x.1 fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} ^ 2 ≤ fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega (S ∪ Sr) ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectedWithinMass_sq_le_reflectedUnion R hq S x y

/--
[fkRectCritical_connectionMass_sq_le_centeredReflectionConnectionMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectCritical_connectionMass_sq_le_centeredReflectionConnectionMass_eq
  {R : FKRectTorus}
  {q : Real}
  {x y : R.Vertex}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x y) ^ 2 ≤ fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x (fkRectDevelopedReflectionVertexEquiv R y.2.val x)) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectionMass_sq_le_centeredReflectionConnectionMass R hq x y

/--
[fkRectDevelopedReflectionVertexEquiv_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionVertexEquiv_fst_eq
  {R : FKRectTorus}
  {center : Nat}
  {v : R.Vertex} :
-- imply
  (fkRectDevelopedReflectionVertexEquiv R center v).1 = v.1 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionVertexEquiv_fst R center v

/--
[fkRectDevelopedThreeByOneEndpointConnection_subset_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneEndpointConnection_subset_carrier_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height) :
-- imply
  fkRectDevelopedThreeByOneEndpointConnectionEvent R n p ⊆ fkRectDevelopedThreeByOneCarrierConnectionEvent R n p := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneEndpointConnection_subset_carrier R n hwidth hheight p

/--
[fkRectDevelopedThreeByOneCarrierConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneCarrierConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)} :
-- imply
  IsIncreasing (fkRectDevelopedThreeByOneCarrierConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneCarrierConnectionEvent_isIncreasing R n p

/--
[fkRectDevelopedThreeByOneTorusCarrier_column_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneTorusCarrier_column_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {v : R.Vertex}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hv : v ∈ fkRectDevelopedThreeByOneTorusCarrier R n) :
-- imply
  1 ≤ v.1.val ∧ v.1.val ≤ 4 * n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneTorusCarrier_column_bounds R n hn hwidth hheight hv

/--
[fkRectDevelopedThreeByOneVertex_row_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneVertex_row_val_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : fkRectDevelopedThreeByOneRect n}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height) :
-- imply
  ((fkRectDevelopedSquareVertex R n z.1).2.val : Int) = z.1 0 - z.1 1 + n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneVertex_row_val R n hwidth hheight z

/--
[fkRectDevelopedThreeByOneEndpoint_row_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneEndpoint_row_sub_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hp : p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n) :
-- imply
  ((fkRectDevelopedSquareVertex R n p.2).2.val : Int) - (fkRectDevelopedSquareVertex R n p.1).2.val = p.2.1 0 - p.1.1 0 - n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneEndpoint_row_sub R n hwidth hheight p hp

/--
[fkRectDevelopedReflectionSet_column_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedReflectionSet_column_bounds_eq
  {R : FKRectTorus}
  {center left right : Nat}
  {S : Set R.Vertex}
  {v : R.Vertex}
-- given
  (hS : ∀ v ∈ S, left ≤ v.1.val ∧ v.1.val ≤ right)
  (hv : v ∈ fkRectDevelopedReflectionSet R center S) :
-- imply
  left ≤ v.1.val ∧ v.1.val ≤ right := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedReflectionSet_column_bounds R center left right S hS hv

/--
[fkRectDevelopedThreeByOne_reflectedUnion_column_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_reflectedUnion_column_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {center : Nat}
  {v : R.Vertex}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hv : v ∈ fkRectDevelopedThreeByOneTorusCarrier R n ∪ fkRectDevelopedReflectionSet R center (fkRectDevelopedThreeByOneTorusCarrier R n)) :
-- imply
  1 ≤ v.1.val ∧ v.1.val ≤ 4 * n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_reflectedUnion_column_bounds R n hn hwidth hheight center hv

/--
[FKRectConnectedWithin.exists_walk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma exists_walk_support_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hxy : FKRectConnectedWithin R omega S x y) :
-- imply
  ∃ w : (fkRectOpenGraph R omega).Walk x.1 y.1, ∀ v ∈ w.support, v ∈ S := by
-- proof
  apply StatMech.FrontierD.FKRectConnectedWithin.exists_walk_support R omega S x y hxy

/--
[fkRectDevelopedThreeByOne_reflectedCarrierConnection_exists_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_reflectedCarrierConnection_exists_walk_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hconn : let S := fkRectDevelopedThreeByOneTorusCarrier R n let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1 let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2 let center := y.1.2.val let Sr := fkRectDevelopedReflectionSet R center S let xr := fkRectDevelopedReflectionVertexEquiv R center x.1 FKRectConnectedWithin R omega (S ∪ Sr) ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩) :
-- imply
  let S := fkRectDevelopedThreeByOneTorusCarrier R n let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1 let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2 let center := y.1.2.val let xr := fkRectDevelopedReflectionVertexEquiv R center x.1 ∃ w : (fkRectOpenGraph R omega).Walk x.1 xr, ∀ v ∈ w.support, 1 ≤ v.1.val ∧ v.1.val ≤ 4 * n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_reflectedCarrierConnection_exists_walk R n hn hwidth hheight omega p hconn

/--
[fkRectCritical_developedThreeByOne_exists_reflectedRowConnection_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_reflectedRowConnection_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n, let x := fkRectDevelopedSquareVertex R n p.1 let y := fkRectDevelopedSquareVertex R n p.2 (1 / (2 * (1 + q)) / (((3 * n + 1) ^ 2 : Nat) : Real)) ^ 2 ≤ fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x (fkRectDevelopedReflectionVertexEquiv R y.2.val x)) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_reflectedRowConnection_ge R n hn hwidth hheight hq

/--
[fkRectCritical_developedThreeByOne_exists_reflectedCarrierConnection_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_reflectedCarrierConnection_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n, let S := fkRectDevelopedThreeByOneTorusCarrier R n let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1 let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2 let center := y.1.2.val let Sr := fkRectDevelopedReflectionSet R center S let xr := fkRectDevelopedReflectionVertexEquiv R center x.1 (1 / (2 * (1 + q)) / (((3 * n + 1) ^ 2 : Nat) : Real)) ^ 2 ≤ fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega (S ∪ Sr) ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_reflectedCarrierConnection_ge R n hn hwidth hheight hq


-- created on 2026-10-23
