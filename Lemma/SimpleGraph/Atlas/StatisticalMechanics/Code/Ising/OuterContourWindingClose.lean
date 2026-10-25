import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.OuterContourWindingClose.Part3
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[latticeOn_reachable_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma latticeOn_reachable_mem_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ S)
  (hxy : (latticeOn S).Reachable x y) :
-- imply
  y ∈ S := by
-- proof
  apply StatMech.Ising.latticeOn_reachable_mem hx hxy

/--
[mem_outerExteriorComponent_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma mem_outerExteriorComponent_of_exterior_eq
  {S : Set (Site 2)}
  {n : ℕ}
  {x : Site 2}
-- given
  (hS : S ⊆ box 2 n)
  (hx : x ∈ exterior 2 n) :
-- imply
  x ∈ outerExteriorComponent S n := by
-- proof
  apply StatMech.Ising.mem_outerExteriorComponent_of_exterior hS hx

/--
[subset_spinCompatibleFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma subset_spinCompatibleFill_eq
  {S : Set (Site 2)}
  {n : ℕ}
-- given
  (hS : S ⊆ box 2 n) :
-- imply
  S ⊆ spinCompatibleFill S n := by
-- proof
  apply StatMech.Ising.subset_spinCompatibleFill hS

/--
[spinCompatibleFill_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_subset_box_eq
  {S : Set (Site 2)}
  {n : ℕ}
-- given
  (hS : S ⊆ box 2 n) :
-- imply
  spinCompatibleFill S n ⊆ box 2 n := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_subset_box hS

/--
[mem_outerExteriorComponent_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma mem_outerExteriorComponent_adj_iff_eq
  {S : Set (Site 2)}
  {n : ℕ}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hxS : x ∉ S)
  (hyS : y ∉ S) :
-- imply
  x ∈ outerExteriorComponent S n ↔ y ∈ outerExteriorComponent S n := by
-- proof
  apply StatMech.Ising.mem_outerExteriorComponent_adj_iff hadj hxS hyS

/--
[outerExteriorComponent_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma outerExteriorComponent_reachable_eq
  {S : Set (Site 2)}
  {n : ℕ}
  {x y : Site 2}
-- given
  (hx : x ∈ outerExteriorComponent S n)
  (hy : y ∈ outerExteriorComponent S n) :
-- imply
  (latticeOn (outerExteriorComponent S n)).Reachable x y := by
-- proof
  apply StatMech.Ising.outerExteriorComponent_reachable hx hy

/--
[spinCompatibleFill_compl_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_compl_reachable_eq
  {S : Set (Site 2)}
  {n : ℕ}
  {x y : Site 2}
-- given
  (hx : x ∈ (spinCompatibleFill S n)ᶜ)
  (hy : y ∈ (spinCompatibleFill S n)ᶜ) :
-- imply
  (latticeOn (spinCompatibleFill S n)ᶜ).Reachable x y := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_compl_reachable hx hy

/--
[spinCompatibleFill_reaches_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_reaches_set_eq
  {S : Set (Site 2)}
  {n : ℕ}
  {x : Site 2}
-- given
  (hS : S ⊆ box 2 n)
  (hx : x ∈ spinCompatibleFill S n) :
-- imply
  ∃ z ∈ S, (latticeOn (spinCompatibleFill S n)).Reachable x z := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_reaches_set hS hx

/--
[spinCompatibleFill_connected_from](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_connected_from_eq
  {S : Set (Site 2)}
  {n : ℕ}
  {o : Site 2}
-- given
  (hS : S ⊆ box 2 n)
  (hconn : ∀ z ∈ S, (latticeOn S).Reachable o z) :
-- imply
  ∀ x ∈ spinCompatibleFill S n, (latticeOn (spinCompatibleFill S n)).Reachable o x := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_connected_from hS hconn

/--
[crosses_of_spinCompatibleFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma crosses_of_spinCompatibleFill_eq
  {S : Set (Site 2)}
  {n : ℕ}
  {x y : Site 2}
-- given
  (hS : S ⊆ box 2 n)
  (hadj : (hypercubicLattice 2).Adj x y)
  (hcross : crosses (spinCompatibleFill S n) s(x, y)) :
-- imply
  crosses S s(x, y) := by
-- proof
  apply StatMech.Ising.crosses_of_spinCompatibleFill hS hadj hcross

/--
[spinCompatibleFill_contourEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_contourEvent_eq
  {n : ℕ}
-- given
  (τ : {x // x ∈ box 2 n} → Bool)
  (ho : glue (plusField 2) τ (origin 2) = false) :
-- imply
  ContourEvent (spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n) (bondFinsetTouch 2 n) (glue (plusField 2) τ) := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_contourEvent τ ho

/--
[spinCompatibleFill_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_finite_eq
  {n : ℕ}
-- given
  (τ : {x // x ∈ box 2 n} → Bool)
  (ho : glue (plusField 2) τ (origin 2) = false) :
-- imply
  (spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n).Finite := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_finite τ ho

/--
[coe_spinCompatibleFillFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma coe_spinCompatibleFillFinset_eq
  {n : ℕ}
-- given
  (τ : {x // x ∈ box 2 n} → Bool)
  (ho : glue (plusField 2) τ (origin 2) = false) :
-- imply
  (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) = spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n := by
-- proof
  apply StatMech.Ising.coe_spinCompatibleFillFinset τ ho

/--
[spinCompatibleFillFinset_isConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFillFinset_isConnected_eq
  {n : ℕ}
-- given
  (τ : {x // x ∈ box 2 n} → Bool)
  (ho : glue (plusField 2) τ (origin 2) = false) :
-- imply
  IsConnectedCluster (spinCompatibleFillFinset τ ho) := by
-- proof
  apply StatMech.Ising.spinCompatibleFillFinset_isConnected τ ho

/--
[spinCompatibleFillFinset_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFillFinset_core_eq
  {n : ℕ}
-- given
  (τ : {x // x ∈ box 2 n} → Bool)
  (ho : glue (plusField 2) τ (origin 2) = false) :
-- imply
  (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster (spinCompatibleFillFinset τ ho) ∧ ContourEvent (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) := by
-- proof
  apply StatMech.Ising.spinCompatibleFillFinset_core τ ho

/--
[latticeOn_le_latticeMinusBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma latticeOn_le_latticeMinusBarrier_eq
  {S : Set (Site 2)} :
-- imply
  latticeOn S ≤ latticeMinusBarrier S := by
-- proof
  apply StatMech.Ising.latticeOn_le_latticeMinusBarrier S

/--
[latticeOn_compl_le_latticeMinusBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma latticeOn_compl_le_latticeMinusBarrier_eq
  {S : Set (Site 2)} :
-- imply
  latticeOn Sᶜ ≤ latticeMinusBarrier S := by
-- proof
  apply StatMech.Ising.latticeOn_compl_le_latticeMinusBarrier S

/--
[spinCompatibleFillFinset_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFillFinset_faceBoundaryConnected_eq
  {n : ℕ}
-- given
  (τ : {x // x ∈ box 2 n} → Bool)
  (ho : glue (plusField 2) τ (origin 2) = false) :
-- imply
  FaceBoundaryConnected (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) (phb_boundarySupport (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) (spinCompatibleFillFinset τ ho).finite_toSet) := by
-- proof
  apply StatMech.Ising.spinCompatibleFillFinset_faceBoundaryConnected τ ho

/--
[spinCompatibleFillFinset_planarCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFillFinset_planarCore_eq
  {n : ℕ}
-- given
  (τ : {x // x ∈ box 2 n} → Bool)
  (ho : glue (plusField 2) τ (origin 2) = false) :
-- imply
  (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster (spinCompatibleFillFinset τ ho) ∧ ContourEvent (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧ ∃ T : Finset (Site 2), (faceBoundaryGraph (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧ FaceBoundaryConnected (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) T := by
-- proof
  apply StatMech.Ising.spinCompatibleFillFinset_planarCore τ ho

/--
[axisAnchor_of_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma axisAnchor_of_faceBoundaryConnected_eq
  {n : ℕ}
  {K : Finset (Site 2)}
  {T : Finset (Site 2)}
-- given
  (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n)
  (hKconn : IsConnectedCluster K)
  (hsupp : (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)))
  (hconn : FaceBoundaryConnected (↑K : Set (Site 2)) T) :
-- imply
  ∃ j : ℕ, j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧ axisVertex 2 j ∈ T := by
-- proof
  apply StatMech.Ising.axisAnchor_of_faceBoundaryConnected hKbox hKconn hsupp hconn

/--
[spinCompatibleFill_outerContourFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_outerContourFill_eq
  {n : ℕ} :
-- imply
  OuterContourFill n := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_outerContourFill n

/--
[outerContourWinding_of_outerContourFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma outerContourWinding_of_outerContourFill_eq
  {n : ℕ}
-- given
  (h : OuterContourFill n) :
-- imply
  OuterContourWinding n := by
-- proof
  apply StatMech.Ising.outerContourWinding_of_outerContourFill n h

/--
[spinCompatibleFill_outerContourWinding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma spinCompatibleFill_outerContourWinding_eq
  {n : ℕ} :
-- imply
  OuterContourWinding n := by
-- proof
  apply StatMech.Ising.spinCompatibleFill_outerContourWinding n

/--
[peierls_long_range_order_of_outerFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma peierls_long_range_order_of_outerFill_eq
-- given
  (hFill : ∀ n : ℕ, OuterContourFill n) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Ising.peierls_long_range_order_of_outerFill hFill

/--
[peierls_long_range_order_spinCompatibleFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma peierls_long_range_order_spinCompatibleFill_eq :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Ising.peierls_long_range_order_spinCompatibleFill

/--
[singletonOrigin_outerContourFill_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma singletonOrigin_outerContourFill_data_eq
  {n : ℕ} :
-- imply
  (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support ⊆ (singletonBoundarySupport : Set (Site 2)) ∧ FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) singletonBoundarySupport ∧ 0 < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧ axisVertex 2 0 ∈ singletonBoundarySupport := by
-- proof
  apply StatMech.Ising.singletonOrigin_outerContourFill_data n

/--
[isoOriginCompletion_origin_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma isoOriginCompletion_origin_false_eq
  {n : ℕ} :
-- imply
  glue (plusField 2) (isoOriginCompletion n) (origin 2) = false := by
-- proof
  apply StatMech.Ising.isoOriginCompletion_origin_false n

/--
[isoOriginCompletion_ne_origin_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma isoOriginCompletion_ne_origin_true_eq
  {n : ℕ}
  {x : Site 2}
-- given
  (hx : x ≠ origin 2) :
-- imply
  glue (plusField 2) (isoOriginCompletion n) x = true := by
-- proof
  apply StatMech.Ising.isoOriginCompletion_ne_origin_true n hx

/--
[isoOriginCompletion_minusCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma isoOriginCompletion_minusCluster_eq
  {n : ℕ} :
-- imply
  minusCluster (glue (plusField 2) (isoOriginCompletion n)) (origin 2) = (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
-- proof
  apply StatMech.Ising.isoOriginCompletion_minusCluster n

/--
[singletonOrigin_contourEvent_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma singletonOrigin_contourEvent_iso_eq
  {n : ℕ} :
-- imply
  ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) (isoOriginCompletion n)) := by
-- proof
  apply StatMech.Ising.singletonOrigin_contourEvent_iso n

/--
[outerContourFill_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean)
-/
@[path]
private lemma outerContourFill_nonvacuous_eq
  {n : ℕ} :
-- imply
  ∃ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false ∧ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧ ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧ ∃ (T : Finset (Site 2)) (j : ℕ), (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧ FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) T ∧ j < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧ axisVertex 2 j ∈ T := by
-- proof
  apply StatMech.Ising.outerContourFill_nonvacuous n


-- created on 2026-10-23
