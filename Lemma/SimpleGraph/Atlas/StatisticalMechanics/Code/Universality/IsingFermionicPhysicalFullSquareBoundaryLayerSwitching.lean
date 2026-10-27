import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part4
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundary_openSub_eq_closePerimeter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_openSub_eq_closePerimeter_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)} :
-- imply
  openSub (fkIsingSquareBoundaryDeletedPlanar n).G omega = openSub (fkSquareBoxPlanar n).G (fkIsingSquareClosePerimeter n omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_openSub_eq_closePerimeter n omega

/--
[fkIsingSquareClosePerimeter_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareClosePerimeter_setClosed_eq
  {n : Nat}
  {e : Sym2 (fkSquareBoxPlanar n).V}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)} :
-- imply
  fkIsingSquareClosePerimeter n (setClosed e omega) = setClosed e (fkIsingSquareClosePerimeter n omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareClosePerimeter_setClosed n e omega

/--
[fkIsingSquareClosePerimeter_setOpen_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareClosePerimeter_setOpen_of_not_mem_eq
  {n : Nat}
  {e : Sym2 (fkSquareBoxPlanar n).V}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (he : e ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  fkIsingSquareClosePerimeter n (setOpen e omega) = setOpen e (fkIsingSquareClosePerimeter n omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareClosePerimeter_setOpen_of_not_mem n e he omega

/--
[fkIsingSquareBoundaryDeleted_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryDeleted_adj_iff_eq
  {n : Nat}
  {a b : (fkSquareBoxPlanar n).V} :
-- imply
  (fkIsingSquareBoundaryDeletedPlanar n).G.Adj a b ↔ (fkSquareBoxPlanar n).G.Adj a b ∧ s(a, b) ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryDeleted_adj_iff n a b

/--
[fkIsingSquareBoundary_wiring_eq_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_wiring_eq_wired_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring = (fkIsingSquareWiredDobrushinDomain n hn).wiring := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_wiring_eq_wired n hn

/--
[fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  openSub (fkIsingSquareBoundaryDeletedPlanar n).G omega ⊔ (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring = openSub (fkSquareBoxPlanar n).G (fkIsingSquareClosePerimeter n omega) ⊔ (fkIsingSquareWiredDobrushinDomain n hn).wiring := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter n hn omega

/--
[fkIsingSquareBoundary_numClustersBC_eq_closePerimeter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_numClustersBC_eq_closePerimeter_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring omega = numClustersBC (fkSquareBoxPlanar n).G (fkIsingSquareWiredDobrushinDomain n hn).wiring (fkIsingSquareClosePerimeter n omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_numClustersBC_eq_closePerimeter n hn omega

/--
[fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {c : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega c = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (fkIsingSquareClosePerimeter n omega) c := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter n hn omega c

/--
[fkIsingSquareBoundary_one_visit_west_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_one_visit_west_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
  (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east)
  (hopen : forall side, fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 (fkIsingSquareClosePerimeter n omega)) e side) :
-- imply
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_one_visit_west_contour_balance n hn omega e he hwest heast hopen

/--
[fkIsingSquareBoundary_one_visit_east_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_one_visit_east_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
  (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east)
  (hopen : forall side, fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 (fkIsingSquareClosePerimeter n omega)) e side) :
-- imply
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_one_visit_east_contour_balance n hn omega e he hwest heast hopen

/--
[fkIsingSquareBoundary_double_visit_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_double_visit_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east) :
-- imply
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_double_visit_contour_balance n hn omega e he hwest heast

/--
[fkIsingSquareBoundary_fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_fermionicObservable_contour_relation_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn let edges := fkIsingSquareWiredLocalCarrierDarts n e D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) = Complex.I * (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_fermionicObservable_contour_relation n hn e he

/--
[fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquareWiredBondMate n hn d)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate n hn d hsource hterminal

/--
[fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerInwardSide side)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerEndpointSide side)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint n hn side k

/--
[fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementInwardSide side)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (fkIsingSquarePerimeterEdge n side k, fkIsingSquareBoundaryLayerComplementEndpointSide side)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint n hn side k

/--
[fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn z * (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable z ^ 2 = (fkIsingSquareBoundaryPrimitiveIncrement n hn z : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z

/--
[fkIsingSquareBoundaryPrimitiveIncrement_local_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPrimitiveIncrement_local_closed_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) + fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) = fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) + fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPrimitiveIncrement_local_closed n hn e he

/--
[fkIsingSquareInteriorRadialCell_not_mem_perimeter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialCell_not_mem_perimeter_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialCell n} :
-- imply
  e.1.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialCell_not_mem_perimeter n e

/--
[fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n x d)
  (heast : fkIsingSquareDirectionAvailable n x .east)
  (hnorth : fkIsingSquareDirectionAvailable n x .north)
  (hwest : fkIsingSquareDirectionAvailable n x .west)
  (hsouth : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  (fkIsingSquareDirectionEdge n x d hd).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n x d hd heast hnorth hwest hsouth

/--
[fkIsingSquareBoundaryLayerRadialCell_increment_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerRadialCell_increment_closed_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialCell n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryLayerRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .west) + fkIsingSquareBoundaryLayerRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .east) = fkIsingSquareBoundaryLayerRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .south) + fkIsingSquareBoundaryLayerRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .north) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerRadialCell_increment_closed n hn e

/--
[fkIsingSquareBoundary_fermionicObservable_opposite_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_fermionicObservable_opposite_sum_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (e, .west)) + (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (e, .east)) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (e, .south)) + (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_fermionicObservable_opposite_sum n hn e he

/--
[fkIsingSquareBoundaryFullMedialObservable_eq_south_add_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryFullMedialObservable_eq_south_add_north_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  fkIsingSquareBoundaryFullMedialObservable n hn e = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (e, .south)) + (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryFullMedialObservable_eq_south_add_north n hn e he

/--
[fkIsingSquareBoundaryFullMedialObservable_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryFullMedialObservable_projection_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s))) (fkIsingSquareBoundaryFullMedialObservable n hn e) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (e, s)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryFullMedialObservable_projection n hn e he s

/--
[fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
-- imply
  fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, s)) = Complex.normSq (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s))) (fkIsingSquareBoundaryFullMedialObservable n hn e)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection n hn e he s

/--
[fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n)
  (hcode : fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡ fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]) :
-- imply
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable (.dart d.1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq n hn d hcode


-- created on 2026-10-23
