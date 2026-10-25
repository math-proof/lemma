import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part6
open StatMech StatMech.FrontierA


/--
[kwEndpointParameter_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwEndpointParameter_zero_eq
  {M : ℕ}
  {beta alpha : ℝ} :
-- imply
  kwEndpointParameter M beta alpha 0 = 0 := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_zero M beta alpha

/--
[kwEndpointParameter_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwEndpointParameter_last_eq
  {M : ℕ}
  {beta alpha : ℝ} :
-- imply
  kwEndpointParameter M beta alpha (Fin.last (M + 2)) = 1 := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_last M beta alpha

/--
[kwEndpointParameter_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwEndpointParameter_strict_eq
  {M : ℕ}
  {beta alpha : ℝ}
  {k : Fin (M + 2)}
-- given
  (hM : 0 < M)
  (hbeta : 0 < beta)
  (halpha : 0 < alpha)
  (hsum : alpha + beta < 1) :
-- imply
  kwEndpointParameter M beta alpha k.castSucc < kwEndpointParameter M beta alpha k.succ := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_strict M beta alpha hM hbeta halpha hsum k

/--
[kwEndpointParameter_step_le_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwEndpointParameter_step_le_inv_eq
  {M : ℕ}
  {beta alpha : ℝ}
  {k : Fin (M + 2)}
-- given
  (hM : 0 < M)
  (hbeta : 0 ≤ beta)
  (halpha : 0 ≤ alpha)
  (hbetaBound : beta ≤ (M : ℝ)⁻¹)
  (halphaBound : alpha ≤ (M : ℝ)⁻¹) :
-- imply
  kwEndpointParameter M beta alpha k.succ - kwEndpointParameter M beta alpha k.castSucc ≤ (M : ℝ)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameter_step_le_inv M beta alpha hM hbeta halpha hbetaBound halphaBound k

/--
[KWStairParameterData.parameter_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma parameter_strictMono_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  StrictMono (data.parameter i) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.parameter_strictMono data i

/--
[kwStairSliceIndex_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairSliceIndex_even_eq
  {S : ℕ}
  [NeZero S]
  {k : Fin S} :
-- imply
  kwStairSliceIndex (kwStairEvenLocal k) = k := by
-- proof
  apply StatMech.FrontierA.kwStairSliceIndex_even k

/--
[kwStairSliceIndex_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairSliceIndex_odd_eq
  {S : ℕ}
  [NeZero S]
  {k : Fin S} :
-- imply
  kwStairSliceIndex (kwStairOddLocal k) = k := by
-- proof
  apply StatMech.FrontierA.kwStairSliceIndex_odd k

/--
[kwStairEvenLocal_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairEvenLocal_mod_two_eq
  {S : ℕ}
  [NeZero S]
  {k : Fin S} :
-- imply
  (kwStairEvenLocal k).val % 2 = 0 := by
-- proof
  apply StatMech.FrontierA.kwStairEvenLocal_mod_two k

/--
[kwStairOddLocal_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairOddLocal_mod_two_eq
  {S : ℕ}
  [NeZero S]
  {k : Fin S} :
-- imply
  (kwStairOddLocal k).val % 2 = 1 := by
-- proof
  apply StatMech.FrontierA.kwStairOddLocal_mod_two k

/--
[KWStairParameterData.localVertex_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma localVertex_even_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.localVertex i (kwStairEvenLocal k) = data.base i k.castSucc := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_even data i k

/--
[KWStairParameterData.localVertex_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma localVertex_odd_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.localVertex i (kwStairOddLocal k) = data.corner i k := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_odd data i k

/--
[kwStairLocal_even_or_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairLocal_even_or_odd_eq
  {S : ℕ}
  [NeZero S]
  {l : Fin (2 * S)} :
-- imply
  ∃ k : Fin S, l = kwStairEvenLocal k ∨ l = kwStairOddLocal k := by
-- proof
  apply StatMech.FrontierA.kwStairLocal_even_or_odd l

/--
[KWStairParameterData.base_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma base_re_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (S + 1)}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  (data.base i k).re = (polygon.vertex i).re + data.parameter i k * (polygon.edgeVector i).re := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_re data i k

/--
[KWStairParameterData.base_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma base_im_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (S + 1)}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  (data.base i k).im = (polygon.vertex i).im + data.parameter i k * (polygon.edgeVector i).im := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_im data i k

/--
[KWStairParameterData.corner_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma corner_re_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  (data.corner i k).re = (polygon.vertex i).re + data.parameter i k.succ * (polygon.edgeVector i).re := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_re data i k

/--
[KWStairParameterData.corner_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma corner_im_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  (data.corner i k).im = (polygon.vertex i).im + data.parameter i k.castSucc * (polygon.edgeVector i).im := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_im data i k

/--
[KWStairParameterData.vertex_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma vertex_even_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.vertex (kwStairEvenIndex i k) = data.base i k.castSucc := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_even data i k

/--
[KWStairParameterData.vertex_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma vertex_odd_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.vertex (kwStairOddIndex i k) = data.corner i k := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_odd data i k

/--
[kwStairEvenIndex_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairEvenIndex_add_one_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {i : Fin n}
  {k : Fin S} :
-- imply
  kwStairEvenIndex i k + 1 = kwStairOddIndex i k := by
-- proof
  apply StatMech.FrontierA.kwStairEvenIndex_add_one i k

/--
[kwStairOddIndex_castSucc_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairOddIndex_castSucc_add_one_eq
  {n M : ℕ}
  [NeZero n]
  {i : Fin n}
  {k : Fin M} :
-- imply
  kwStairOddIndex (S := M + 1) i k.castSucc + 1 = kwStairEvenIndex (S := M + 1) i k.succ := by
-- proof
  apply StatMech.FrontierA.kwStairOddIndex_castSucc_add_one i k

/--
[kwStairOddIndex_last_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma kwStairOddIndex_last_add_one_eq
  {n M : ℕ}
  [NeZero n]
  {i : Fin n} :
-- imply
  kwStairOddIndex (S := M + 1) i (Fin.last M) + 1 = kwStairEvenIndex (S := M + 1) (i + 1) 0 := by
-- proof
  apply StatMech.FrontierA.kwStairOddIndex_last_add_one i

/--
[KWStairParameterData.base_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma base_zero_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.base i 0 = polygon.vertex i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_zero data i

/--
[KWStairParameterData.base_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma base_last_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.base i (Fin.last S) = polygon.vertex (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_last data i

/--
[KWStairParameterData.vertex_odd_castSucc_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma vertex_odd_castSucc_succ_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin M}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  data.vertex (kwStairOddIndex i k.castSucc + 1) = data.base i k.succ.castSucc := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_odd_castSucc_succ data i k

/--
[KWStairParameterData.vertex_odd_last_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma vertex_odd_last_succ_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  data.vertex (kwStairOddIndex i (Fin.last M) + 1) = polygon.vertex (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_odd_last_succ data i

/--
[lineMap_sub_lineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma lineMap_sub_lineMap_eq
  {a b : ℂ}
  {s t : ℝ} :
-- imply
  AffineMap.lineMap a b t - AffineMap.lineMap a b s = (t - s) * (b - a) := by
-- proof
  apply StatMech.FrontierA.lineMap_sub_lineMap a b s t

/--
[KWStairParameterData.corner_sub_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma corner_sub_base_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.corner i k - data.base i k.castSucc = (data.parameter i k.succ - data.parameter i k.castSucc) * kwHorizontalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_sub_base data i k

/--
[KWStairParameterData.base_succ_sub_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma base_succ_sub_corner_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.base i k.succ - data.corner i k = (data.parameter i k.succ - data.parameter i k.castSucc) * kwVerticalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_succ_sub_corner data i k

/--
[KWStairParameterData.vertex_succ_sub_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma vertex_succ_sub_even_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.vertex (kwStairEvenIndex i k + 1) - data.vertex (kwStairEvenIndex i k) = (data.parameter i k.succ - data.parameter i k.castSucc) * kwHorizontalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_succ_sub_even data i k

/--
[KWStairParameterData.vertex_succ_sub_odd_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma vertex_succ_sub_odd_castSucc_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin M}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  data.vertex (kwStairOddIndex i k.castSucc + 1) - data.vertex (kwStairOddIndex i k.castSucc) = (data.parameter i k.castSucc.succ - data.parameter i k.castSucc.castSucc) * kwVerticalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_succ_sub_odd_castSucc data i k

/--
[KWStairParameterData.vertex_succ_sub_odd_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma vertex_succ_sub_odd_last_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := M + 1) polygon) :
-- imply
  data.vertex (kwStairOddIndex i (Fin.last M) + 1) - data.vertex (kwStairOddIndex i (Fin.last M)) = (data.parameter i (Fin.last M).succ - data.parameter i (Fin.last M).castSucc) * kwVerticalPart (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.vertex_succ_sub_odd_last data i

/--
[KWStairParameterData.localVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma localVertex_injective_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0) :
-- imply
  Function.Injective (data.localVertex i) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_injective data hcoords i

/--
[KWStairParameterData.parameter_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma parameter_mem_Icc_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (S + 1)}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.parameter i k ∈ Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.parameter_mem_Icc data i k

/--
[KWStairParameterData.base_mem_closedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma base_mem_closedEdge_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin (S + 1)}
-- given
  (data : KWStairParameterData (S := S) polygon) :
-- imply
  data.base i k ∈ polygon.closedEdge i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_mem_closedEdge data i k

/--
[KWStairParameterData.corner_mem_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma corner_mem_closedEdgeTube_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hfine : data.MeshWithin r) :
-- imply
  data.corner i k ∈ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_mem_closedEdgeTube data r hfine i k

/--
[KWStairParameterData.localVertex_mem_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma localVertex_mem_closedEdgeTube_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {l : Fin (2 * S)}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r) :
-- imply
  data.localVertex i l ∈ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_mem_closedEdgeTube data r hr hfine i l

/--
[KWStairParameterData.localVertex_ne_of_tubes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma localVertex_ne_of_tubes_disjoint_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
  {l q : Fin (2 * S)}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r)
  (hdisjoint : Disjoint (polygon.closedEdgeTube r i) (polygon.closedEdgeTube r j)) :
-- imply
  data.localVertex i l ≠ data.localVertex j q := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_ne_of_tubes_disjoint data r hr hfine hdisjoint l q

/--
[KWStairParameterData.localVertex_ne_of_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma localVertex_ne_of_nonincident_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
  {l q : Fin (2 * S)}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin (r / 2))
  (hsep : ∀ i j : Fin n, KWEdgesNonincident i j → ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j, (r : ℝ) < dist x y)
  (hij : KWEdgesNonincident i j) :
-- imply
  data.localVertex i l ≠ data.localVertex j q := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.localVertex_ne_of_nonincident data r hr hfine hsep hij l q

/--
[KWFiniteSimplePolygon.exists_fine_endpointParameterData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean)
-/
@[path]
private lemma exists_fine_endpointParameterData_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (r : ℝ≥0)
  (hr : 0 < r) :
-- imply
  ∃ M : ℕ, ∃ beta : ℝ, ∃ alpha : Fin n → ℝ, ∃ data : KWStairParameterData (S := M + 2) polygon, 0 < M ∧ 0 < beta ∧ beta < 1 / 4 ∧ (∀ i, 0 < alpha i ∧ alpha i < beta) ∧ (∀ i, |alpha i * (-polygon.edgeVector (i - 1)).re| < |beta * (polygon.edgeVector i).re|) ∧ data.MeshWithin r := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_fine_endpointParameterData polygon hcoords r hr


-- created on 2026-10-23
