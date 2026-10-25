import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealHomotopy
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealAxisHomotopyVertex_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopyVertex_zero_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealAxisHomotopyVertex 0 = patch.idealVertex := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopyVertex_zero patch

/--
[KWAdaptivePatchedData.idealAxisHomotopyVertex_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopyVertex_one_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealAxisHomotopyVertex 1 = patch.vertex := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopyVertex_one patch

/--
[KWAdaptivePatchedData.idealAxisHomotopyVertex_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopyVertex_continuous_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin (n * (2 * (M + 1)))}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  Continuous fun t ↦ patch.idealAxisHomotopyVertex t j := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopyVertex_continuous patch j

/--
[KWAdaptivePatchedData.idealAxisHomotopy_rawEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_rawEdge_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {t : ℝ}
  {j : Fin (n * (2 * (M + 1)))}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge (patch.idealAxisHomotopyVertex t) j = AffineMap.lineMap (kwRawEdge patch.idealVertex j) (kwRawEdge patch.vertex j) t := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_rawEdge patch t j

/--
[KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_even_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_rawEdge_even_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {t : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge (patch.idealAxisHomotopyVertex t) (kwStairEvenIndex i q.castSucc) = AffineMap.lineMap (((patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) / 2 : ℝ) * polygon.edgeVector i) ((patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * (if patch.sliceUsesVerticalFirst i q then kwVerticalPart (polygon.edgeVector i) else kwHorizontalPart (polygon.edgeVector i))) t := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_even_castSucc patch t i q

/--
[KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_odd_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_rawEdge_odd_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {t : ℝ}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge (patch.idealAxisHomotopyVertex t) (kwStairOddIndex i q.castSucc) = AffineMap.lineMap (((patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) / 2 : ℝ) * polygon.edgeVector i) ((patch.data.parameter i q.succ.castSucc.succ - patch.data.parameter i q.succ.castSucc.castSucc) * (if patch.sliceUsesVerticalFirst i q then kwHorizontalPart (polygon.edgeVector i) else kwVerticalPart (polygon.edgeVector i))) t := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_odd_castSucc patch t i q

/--
[KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_even_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_rawEdge_even_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {t : ℝ}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge (patch.idealAxisHomotopyVertex t) (kwStairEvenIndex i (Fin.last M)) = (patch.connector (i + 1)).corner - patch.alpha (i + 1) * (-polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_even_last patch t i

/--
[KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_odd_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_rawEdge_odd_last_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {t : ℝ}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawEdge (patch.idealAxisHomotopyVertex t) (kwStairOddIndex i (Fin.last M)) = patch.beta * polygon.edgeVector (i + 1) - (patch.connector (i + 1)).corner := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_odd_last patch t i

/--
[KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean)
-/
@[path]
private lemma idealAxisHomotopy_rawEdge_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {t : ℝ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (ht : t ∈ Icc (0 : ℝ) 1) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), kwRawEdge (patch.idealAxisHomotopyVertex t) j ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealAxisHomotopy_rawEdge_ne_zero patch hcoords ht


-- created on 2026-10-23
