import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk.Part4
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.lastMiddleIndex_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma lastMiddleIndex_val_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.lastMiddleIndex.val = M - 1 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.lastMiddleIndex_val patch

/--
[KWAdaptivePatchedData.pathBase_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma pathBase_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.pathBase i q.castSucc = patch.data.base i q.succ.castSucc.castSucc := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_castSucc patch i q

/--
[KWAdaptivePatchedData.pathBase_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma pathBase_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.pathBase i (Fin.last M) = patch.incomingPort i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathBase_last patch i

/--
[KWAdaptivePatchedData.pathCorner_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma pathCorner_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.pathCorner i q.castSucc = patch.middleCorner i q := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathCorner_castSucc patch i q

/--
[KWAdaptivePatchedData.pathCorner_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma pathCorner_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.pathCorner i (Fin.last M) = patch.connectorCorner (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.pathCorner_last patch i

/--
[KWAdaptivePatchedData.localVertex_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma localVertex_even_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.localVertex i (kwStairEvenLocal k) = patch.pathBase i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.localVertex_even patch i k

/--
[KWAdaptivePatchedData.localVertex_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma localVertex_odd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.localVertex i (kwStairOddLocal k) = patch.pathCorner i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.localVertex_odd patch i k

/--
[KWAdaptivePatchedData.vertex_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma vertex_even_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.vertex (kwStairEvenIndex i k) = patch.pathBase i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.vertex_even patch i k

/--
[KWAdaptivePatchedData.vertex_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma vertex_odd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.vertex (kwStairOddIndex i k) = patch.pathCorner i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.vertex_odd patch i k

/--
[KWAdaptivePatchedData.incomingPort_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma incomingPort_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.incomingPort i = polygon.vertex (i + 1) + patch.alpha (i + 1) * (-polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.incomingPort_eq patch i

/--
[KWAdaptivePatchedData.outgoingPort_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma outgoingPort_eq_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.outgoingPort i = polygon.vertex i + patch.beta * polygon.edgeVector i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.outgoingPort_eq patch i

/--
[KWAdaptivePatchedData.middleCorner_sub_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma middleCorner_sub_base_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.middleCorner i q - patch.data.base i q.succ.castSucc.castSucc = (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * (if patch.sliceUsesVerticalFirst i q then kwVerticalPart (polygon.edgeVector i) else kwHorizontalPart (polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.middleCorner_sub_base patch i q

/--
[KWAdaptivePatchedData.base_succ_sub_middleCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma base_succ_sub_middleCorner_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.data.base i q.succ.castSucc.succ - patch.middleCorner i q = (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * (if patch.sliceUsesVerticalFirst i q then kwHorizontalPart (polygon.edgeVector i) else kwVerticalPart (polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.base_succ_sub_middleCorner patch i q

/--
[KWAdaptivePatchedData.rawEdge_even_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma rawEdge_even_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.vertex (kwStairEvenIndex i q.castSucc) = (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * (if patch.sliceUsesVerticalFirst i q then kwVerticalPart (polygon.edgeVector i) else kwHorizontalPart (polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawEdge_even_castSucc patch i q

/--
[KWAdaptivePatchedData.rawEdge_odd_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma rawEdge_odd_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.vertex (kwStairOddIndex i q.castSucc) = (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * (if patch.sliceUsesVerticalFirst i q then kwHorizontalPart (polygon.edgeVector i) else kwVerticalPart (polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawEdge_odd_castSucc patch i q

/--
[KWAdaptivePatchedData.rawEdge_even_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma rawEdge_even_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) = (patch.connector (i + 1)).corner - patch.alpha (i + 1) * (-polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawEdge_even_last patch i

/--
[KWAdaptivePatchedData.rawEdge_odd_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean)
-/
@[path]
private lemma rawEdge_odd_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.vertex (kwStairOddIndex i (Fin.last M)) = patch.beta * polygon.edgeVector (i + 1) - (patch.connector (i + 1)).corner := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.rawEdge_odd_last patch i


-- created on 2026-10-23
