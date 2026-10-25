import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseCorePlacement
open StatMech StatMech.FrontierA


/--
[KWStairParameterData.base_mem_closedEdgeCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma base_mem_closedEdgeCore_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin (S + 1)}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (hk : data.parameter i k ∈ Icc eps (1 - eps)) :
-- imply
  data.base i k ∈ polygon.closedEdgeCore eps i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_mem_closedEdgeCore data i k hk

/--
[KWStairParameterData.base_mem_closedEdgeCoreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma base_mem_closedEdgeCoreTube_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin (S + 1)}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hk : data.parameter i k ∈ Icc eps (1 - eps)) :
-- imply
  data.base i k ∈ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.base_mem_closedEdgeCoreTube data r hr i k hk

/--
[KWStairParameterData.corner_mem_closedEdgeCoreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma corner_mem_closedEdgeCoreTube_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hfine : data.MeshWithin r)
  (hk : data.parameter i k.castSucc ∈ Icc eps (1 - eps)) :
-- imply
  data.corner i k ∈ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_mem_closedEdgeCoreTube data r hfine i k hk

/--
[KWStairParameterData.corner_mem_closedEdgeCoreTube_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma corner_mem_closedEdgeCoreTube_of_step_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hk : data.parameter i k.castSucc ∈ Icc eps (1 - eps))
  (hstep : (data.parameter i k.succ - data.parameter i k.castSucc) * ‖polygon.edgeVector i‖ < r) :
-- imply
  data.corner i k ∈ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.corner_mem_closedEdgeCoreTube_of_step data r i k hk hstep

/--
[KWStairParameterData.rawClosedEdge_even_subset_closedEdgeCoreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma rawClosedEdge_even_subset_closedEdgeCoreTube_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin S}
-- given
  (data : KWStairParameterData (S := S) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r)
  (hk : data.parameter i k.castSucc ∈ Icc eps (1 - eps)) :
-- imply
  kwRawClosedEdge data.vertex (kwStairEvenIndex i k) ⊆ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_even_subset_closedEdgeCoreTube data r hr hfine i k hk

/--
[KWStairParameterData.rawClosedEdge_odd_castSucc_subset_closedEdgeCoreTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma rawClosedEdge_odd_castSucc_subset_closedEdgeCoreTube_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin M}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hfine : data.MeshWithin r)
  (hk : data.parameter i k.castSucc.castSucc ∈ Icc eps (1 - eps))
  (hnext : data.parameter i k.castSucc.succ ∈ Icc eps (1 - eps)) :
-- imply
  kwRawClosedEdge data.vertex (kwStairOddIndex i k.castSucc) ⊆ polygon.closedEdgeCoreTube eps r i := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_odd_castSucc_subset_closedEdgeCoreTube data r hr hfine i k hk hnext

/--
[KWStairParameterData.parameter_mem_core_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma parameter_mem_core_of_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta : ℝ}
  {incoming : Fin n → ℝ}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin (M + 1)}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hfirst : ∀ i : Fin n, data.parameter i (0 : Fin (M + 1)).succ = beta)
  (hlast : ∀ i : Fin n, data.parameter i (Fin.last M).castSucc = 1 - incoming i)
  (hepsBeta : eps ≤ beta)
  (hepsIncoming : ∀ i, eps ≤ incoming i)
  (hk : k ≠ 0) :
-- imply
  data.parameter i k.castSucc ∈ Icc eps (1 - eps) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.parameter_mem_core_of_ne_zero data beta incoming hfirst hlast hepsBeta hepsIncoming i k hk

/--
[kwEndpointParameterData_parameter_mem_core_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma kwEndpointParameterData_parameter_mem_core_of_ne_zero_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta : ℝ}
  {alpha : Fin n → ℝ}
  {eps : ℝ}
  {i : Fin n}
  {k : Fin (M + 2)}
-- given
  (hM : 0 < M)
  (hbeta : 0 < beta)
  (halpha : ∀ i, 0 < alpha i)
  (hsum : ∀ i, alpha i + beta < 1)
  (hepsBeta : eps ≤ beta)
  (hepsAlpha : ∀ i, eps ≤ alpha i)
  (hk : k ≠ 0) :
-- imply
  let data := kwEndpointParameterData polygon M beta alpha hM hbeta halpha hsum data.parameter i k.castSucc ∈ Icc eps (1 - eps) := by
-- proof
  apply StatMech.FrontierA.kwEndpointParameterData_parameter_mem_core_of_ne_zero polygon beta alpha hM hbeta halpha hsum hepsBeta hepsAlpha i k hk

/--
[exists_common_endpoint_core_trim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma exists_common_endpoint_core_trim_eq
  {n : ℕ}
  [NeZero n]
  {beta : ℝ}
  {alpha : Fin n → ℝ}
-- given
  (hbeta : 0 < beta)
  (hbetaQuarter : beta < 1 / 4)
  (halpha : ∀ i, 0 < alpha i) :
-- imply
  ∃ eps : ℝ, 0 < eps ∧ eps < 1 / 2 ∧ eps ≤ beta ∧ ∀ i, eps ≤ alpha i := by
-- proof
  apply StatMech.FrontierA.exists_common_endpoint_core_trim beta alpha hbeta hbetaQuarter halpha

/--
[KWFiniteSimplePolygon.exists_fixedEndpointParameterData_meshWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma exists_fixedEndpointParameterData_meshWithin_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta : ℝ}
  {alpha : Fin n → ℝ}
-- given
  (hbeta : 0 < beta)
  (halpha : ∀ i, 0 < alpha i)
  (hsum : ∀ i, alpha i + beta < 1)
  (r : ℝ≥0)
  (hr : 0 < r)
  (hbetaMesh : ∀ i : Fin n, beta * ‖polygon.edgeVector i‖ < r)
  (halphaMesh : ∀ i : Fin n, alpha (i + 1) * ‖polygon.edgeVector i‖ < r) :
-- imply
  ∃ M : ℕ, ∃ data : KWStairParameterData (S := M + 2) polygon, 0 < M ∧ data.MeshWithin r := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_fixedEndpointParameterData_meshWithin polygon beta alpha hbeta halpha hsum r hr hbetaMesh halphaMesh

/--
[KWFiniteSimplePolygon.exists_fixedEndpointParameterData_interiorMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseCorePlacement.lean)
-/
@[path]
private lemma exists_fixedEndpointParameterData_interiorMesh_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {beta : ℝ}
  {alpha : Fin n → ℝ}
-- given
  (hbeta : 0 < beta)
  (halpha : ∀ i, 0 < alpha i)
  (hsum : ∀ i, alpha i + beta < 1)
  (r : ℝ≥0)
  (hr : 0 < r) :
-- imply
  ∃ M : ℕ, ∃ data : KWStairParameterData (S := M + 2) polygon, 0 < M ∧ KWEndpointInteriorMeshWithin data r := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_fixedEndpointParameterData_interiorMesh polygon beta alpha hbeta halpha hsum r hr


-- created on 2026-10-23
