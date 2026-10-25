import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealWalk.Part3
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealPathCorner_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealPathCorner_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealPathCorner i q.castSucc = patch.idealMiddleCorner i q := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealPathCorner_castSucc patch i q

/--
[KWAdaptivePatchedData.idealPathCorner_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealPathCorner_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealPathCorner i (Fin.last M) = patch.connectorCorner (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealPathCorner_last patch i

/--
[KWAdaptivePatchedData.idealLocalVertex_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealLocalVertex_even_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealLocalVertex i (kwStairEvenLocal k) = patch.pathBase i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealLocalVertex_even patch i k

/--
[KWAdaptivePatchedData.idealLocalVertex_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealLocalVertex_odd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealLocalVertex i (kwStairOddLocal k) = patch.idealPathCorner i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealLocalVertex_odd patch i k

/--
[KWAdaptivePatchedData.idealVertex_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealVertex_even_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealVertex (kwStairEvenIndex i k) = patch.pathBase i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealVertex_even patch i k

/--
[KWAdaptivePatchedData.idealVertex_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealVertex_odd_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealVertex (kwStairOddIndex i k) = patch.idealPathCorner i k := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealVertex_odd patch i k

/--
[KWAdaptivePatchedData.idealMiddleCorner_sub_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealMiddleCorner_sub_base_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealMiddleCorner i q - patch.data.base i q.succ.castSucc.castSucc = (1 / 2 : ℝ) * (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * polygon.edgeVector i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleCorner_sub_base patch i q

/--
[KWAdaptivePatchedData.base_succ_sub_idealMiddleCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma base_succ_sub_idealMiddleCorner_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.data.base i q.succ.castSucc.succ - patch.idealMiddleCorner i q = (1 / 2 : ℝ) * (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * polygon.edgeVector i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.base_succ_sub_idealMiddleCorner patch i q

/--
[KWAdaptivePatchedData.idealRawEdge_even_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealRawEdge_even_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) = (1 / 2 : ℝ) * (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * polygon.edgeVector i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawEdge_even_castSucc patch i q

/--
[KWAdaptivePatchedData.idealRawEdge_odd_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealRawEdge_odd_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.idealVertex (kwStairOddIndex i q.castSucc) = (1 / 2 : ℝ) * (patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * polygon.edgeVector i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawEdge_odd_castSucc patch i q

/--
[KWAdaptivePatchedData.idealRawEdge_even_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealRawEdge_even_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) = (patch.connector (i + 1)).corner - patch.alpha (i + 1) * (-polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawEdge_even_last patch i

/--
[KWAdaptivePatchedData.idealRawEdge_odd_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealWalk.lean)
-/
@[path]
private lemma idealRawEdge_odd_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge patch.idealVertex (kwStairOddIndex i (Fin.last M)) = patch.beta * polygon.edgeVector (i + 1) - (patch.connector (i + 1)).corner := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawEdge_odd_last patch i


-- created on 2026-10-23
