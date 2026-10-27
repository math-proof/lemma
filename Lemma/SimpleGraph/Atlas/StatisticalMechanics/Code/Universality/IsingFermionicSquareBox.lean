import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundarySite_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundarySite_mem_box_eq
  {n : Nat}
  {i : FKIsingSquareBoundaryIndex n} :
-- imply
  fkIsingSquareBoundarySite n i ∈ box 2 n := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundarySite_mem_box n i

/--
[fkIsingSquareBoundaryOrderKey_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryOrderKey_lt_eq
  {n : Nat}
  {i : FKIsingSquareBoundaryIndex n} :
-- imply
  fkIsingSquareBoundaryOrderKey n i < 8 * n := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryOrderKey_lt n i

/--
[fkIsingSquareBoundaryOrderKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryOrderKey_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareBoundaryOrderKey n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryOrderKey_injective n

/--
[fkIsingSquareBoundaryOrderFin_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryOrderFin_bijective_eq
  {n : Nat} :
-- imply
  Function.Bijective (fkIsingSquareBoundaryOrderFin n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryOrderFin_bijective n

/--
[fkIsingSquareBoundaryOrder_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryOrder_length_eq
  {n : Nat} :
-- imply
  (fkIsingSquareBoundaryOrder n).length = 8 * n := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryOrder_length n

/--
[fkIsingSquareBoundaryOrder_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryOrder_nodup_eq
  {n : Nat} :
-- imply
  (fkIsingSquareBoundaryOrder n).Nodup := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryOrder_nodup n

/--
[fkIsingSquareBoundarySucc_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundarySucc_ne_eq
  {n : Nat}
  {i : FKIsingSquareBoundaryIndex n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundarySucc n hn i ≠ i := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundarySucc_ne n hn i

/--
[fkIsingSquareBoundaryVertex_markedA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryVertex_markedA_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryVertex n (fkIsingSquareMarkedAIndex n hn) = fkIsingSquareMarkedA n := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryVertex_markedA n hn

/--
[fkIsingSquareBoundaryVertex_markedB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryVertex_markedB_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryVertex n (fkIsingSquareMarkedBIndex n hn) = fkIsingSquareMarkedB n := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryVertex_markedB n hn

/--
[fkIsingSquareMarkedA_mem_wiredArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareMarkedA_mem_wiredArc_eq
  {n : Nat} :
-- imply
  fkIsingSquareWiredArc n (fkIsingSquareMarkedA n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedA_mem_wiredArc n

/--
[fkIsingSquareMarkedB_mem_wiredArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareMarkedB_mem_wiredArc_eq
  {n : Nat} :
-- imply
  fkIsingSquareWiredArc n (fkIsingSquareMarkedB n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedB_mem_wiredArc n

/--
[fkIsingSquareBoundary_left_mem_wiredArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBoundary_left_mem_wiredArc_eq
  {n : Nat}
  {k : Fin (2 * n)} :
-- imply
  fkIsingSquareWiredArc n (fkIsingSquareBoundaryVertex n (.left, k)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundary_left_mem_wiredArc n k

/--
[fkIsingSquareWiredExteriorStar_le_clique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareWiredExteriorStar_le_clique_eq
  {n : Nat} :
-- imply
  fkIsingSquareWiredExteriorStar n ≤ boundaryCliqueGraph (fkIsingSquareWiredArc n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExteriorStar_le_clique n

/--
[fkIsingSquareWiredExteriorStar_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareWiredExteriorStar_reachable_eq
  {n : Nat}
  {x y : (fkSquareBoxPlanar n).V}
-- given
  (hx : fkIsingSquareWiredArc n x)
  (hy : fkIsingSquareWiredArc n y) :
-- imply
  (fkIsingSquareWiredExteriorStar n).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExteriorStar_reachable n hx hy

/--
[fkIsingSquare_sup_wiredExteriorStar_reachable_iff_clique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_sup_wiredExteriorStar_reachable_iff_clique_eq
  {n : Nat}
  {H : SimpleGraph (fkSquareBoxPlanar n).V}
  {x y : (fkSquareBoxPlanar n).V} :
-- imply
  (H ⊔ fkIsingSquareWiredExteriorStar n).Reachable x y ↔ (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquare_sup_wiredExteriorStar_reachable_iff_clique n H x y

/--
[fkIsingSquareWiredGadgetProjection_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareWiredGadgetProjection_reachable_eq
  {n : Nat}
  {H : SimpleGraph (fkSquareBoxPlanar n).V}
  {x y : FKIsingSquareWiredGadgetVertex n}
-- given
  (hxy : (fkIsingSquareLiftPhysicalGraph n H ⊔ fkIsingSquareWiredExteriorGadget n).Adj x y) :
-- imply
  (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable (fkIsingSquareWiredGadgetProjection n x) (fkIsingSquareWiredGadgetProjection n y) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredGadgetProjection_reachable n H hxy

/--
[fkIsingSquare_wiredExteriorGadget_reachable_iff_clique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_wiredExteriorGadget_reachable_iff_clique_eq
  {n : Nat}
  {H : SimpleGraph (fkSquareBoxPlanar n).V}
  {x y : (fkSquareBoxPlanar n).V} :
-- imply
  (fkIsingSquareLiftPhysicalGraph n H ⊔ fkIsingSquareWiredExteriorGadget n).Reachable (.physical x) (.physical y) ↔ (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
-- proof
  apply StatMech.Universality.fkIsingSquare_wiredExteriorGadget_reachable_iff_clique n H x y

/--
[fkIsingSquareMarkedA_adj_afterA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareMarkedA_adj_afterA_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkSquareBoxPlanar n).G.Adj (fkIsingSquareMarkedA n) (fkIsingSquareAfterA n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedA_adj_afterA n hn

/--
[fkIsingSquareMarkedB_adj_afterB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareMarkedB_adj_afterB_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkSquareBoxPlanar n).G.Adj (fkIsingSquareMarkedB n) (fkIsingSquareAfterB n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedB_adj_afterB n hn

/--
[fkIsingSquareOrientedEdge_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareOrientedEdge_nonempty_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)} :
-- imply
  Nonempty (FKIsingSquareEdgeOrientation n e) := by
-- proof
  apply StatMech.Universality.fkIsingSquareOrientedEdge_nonempty n e

/--
[fkIsingSquareOrientedEdge_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareOrientedEdge_unique_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {a b : FKIsingSquareEdgeOrientation n e} :
-- imply
  a = b := by
-- proof
  apply StatMech.Universality.fkIsingSquareOrientedEdge_unique n e a b

/--
[fkIsingSquareOrientedEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareOrientedEdge_eq_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)} :
-- imply
  s((fkIsingSquareOrientedEdge n e).tail, (fkIsingSquareOrientedEdge n e).head) = e.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareOrientedEdge_eq n e

/--
[fkIsingSquareCornerSide_sideCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCornerSide_sideCorner_eq
  {side : FKIsingMedialSide} :
-- imply
  fkIsingSquareCornerSide (fkIsingSquareSideCorner side) = side := by
-- proof
  apply StatMech.Universality.fkIsingSquareCornerSide_sideCorner side

/--
[fkIsingSquareSideCorner_cornerSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareSideCorner_cornerSide_eq
  {corner : FKIsingSquareEdgeEndpoint × FKIsingSquareCornerTurn} :
-- imply
  fkIsingSquareSideCorner (fkIsingSquareCornerSide corner) = corner := by
-- proof
  apply StatMech.Universality.fkIsingSquareSideCorner_cornerSide corner

/--
[fkIsingSquareDartEndpoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDartEndpoint_mem_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareDartEndpoint n d ∈ d.1.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartEndpoint_mem n d

/--
[fkIsingSquareVertex_coordinate_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareVertex_coordinate_bounds_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {i : Fin 2} :
-- imply
  -(n : Int) ≤ u.1 i ∧ u.1 i ≤ (n : Int) := by
-- proof
  apply StatMech.Universality.fkIsingSquareVertex_coordinate_bounds n u i

/--
[fkIsingSquareNextDirection_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareNextDirection_available_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareDirectionAvailable n u (fkIsingSquareNextDirection n u d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareNextDirection_available n hn u d hd

/--
[fkIsingSquarePreviousDirection_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquarePreviousDirection_available_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareDirectionAvailable n u (fkIsingSquarePreviousDirection n u d) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePreviousDirection_available n hn u d hd

/--
[fkIsingSquarePreviousDirection_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquarePreviousDirection_next_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (_hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquarePreviousDirection n u (fkIsingSquareNextDirection n u d) = d := by
-- proof
  apply StatMech.Universality.fkIsingSquarePreviousDirection_next n _hn u d hd

/--
[fkIsingSquareNextDirection_previous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareNextDirection_previous_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (_hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareNextDirection n u (fkIsingSquarePreviousDirection n u d) = d := by
-- proof
  apply StatMech.Universality.fkIsingSquareNextDirection_previous n _hn u d hd

/--
[fkIsingSquareNeighborSite_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareNeighborSite_mem_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareNeighborSite u.1 d ∈ box 2 n := by
-- proof
  apply StatMech.Universality.fkIsingSquareNeighborSite_mem n u d hd

/--
[fkIsingSquare_adj_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_adj_neighbor_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  (fkSquareBoxPlanar n).G.Adj u (fkIsingSquareNeighbor n u d hd) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_adj_neighbor n u d hd

/--
[fkIsingSquareDartDirection_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDartDirection_available_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartDirection_available n d

/--
[fkIsingSquareOrientedEdge_directionEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareOrientedEdge_directionEdge_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareOrientedEdge n (fkIsingSquareDirectionEdge n u d hd) = fkIsingSquareDirectionEdgeOrientation n u d hd := by
-- proof
  apply StatMech.Universality.fkIsingSquareOrientedEdge_directionEdge n u d hd

/--
[fkIsingSquareDirectionDart_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDirectionDart_endpoint_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareDirectionDart n u d hd turn) = u := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionDart_endpoint n u d hd turn

/--
[fkIsingSquareDirectionDart_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDirectionDart_direction_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareDartDirection n (fkIsingSquareDirectionDart n u d hd turn) = d := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionDart_direction n u d hd turn

/--
[fkIsingSquareDirectionDart_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDirectionDart_turn_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  (fkIsingSquareSideCorner (fkIsingSquareDirectionDart n u d hd turn).2).2 = turn := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionDart_turn n u d hd turn

/--
[fkIsingSquareDirectionDart_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDirectionDart_congr_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d e : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn}
-- given
  (h : d = e)
  (hd : fkIsingSquareDirectionAvailable n u d)
  (he : fkIsingSquareDirectionAvailable n u e) :
-- imply
  fkIsingSquareDirectionDart n u d hd turn = fkIsingSquareDirectionDart n u e he turn := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionDart_congr n u h hd he turn

/--
[fkIsingSquareDirectionEdge_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDirectionEdge_reconstruct_eq
  {n : Nat}
  {x : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareDirectionEdge n (fkIsingSquareDartEndpoint n x) (fkIsingSquareDartDirection n x) (fkIsingSquareDartDirection_available n x) = x.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionEdge_reconstruct n x

/--
[fkIsingSquareDirectionDart_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDirectionDart_reconstruct_eq
  {n : Nat}
  {x : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n x) (fkIsingSquareDartDirection n x) (fkIsingSquareDartDirection_available n x) (fkIsingSquareSideCorner x.2).2 = x := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionDart_reconstruct n x

/--
[fkIsingSquareBondMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_involutive_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Involutive (fkIsingSquareBondMate n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_involutive n hn

/--
[fkIsingSquareDartEndpoint_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDartEndpoint_bondMate_eq
  {n : Nat}
  {x : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareBondMate n hn x) = fkIsingSquareDartEndpoint n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartEndpoint_bondMate n hn x

/--
[fkIsingSquareNextDirection_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareNextDirection_ne_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (_hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareNextDirection n u d ≠ d := by
-- proof
  apply StatMech.Universality.fkIsingSquareNextDirection_ne n _hn u d hd

/--
[fkIsingSquarePreviousDirection_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquarePreviousDirection_ne_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (_hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquarePreviousDirection n u d ≠ d := by
-- proof
  apply StatMech.Universality.fkIsingSquarePreviousDirection_ne n _hn u d hd

/--
[fkIsingSquareNeighbor_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareNeighbor_ne_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareNeighbor n u d hd ≠ u := by
-- proof
  apply StatMech.Universality.fkIsingSquareNeighbor_ne n u d hd

/--
[fkIsingSquareNeighbor_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareNeighbor_injective_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d e : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d)
  (he : fkIsingSquareDirectionAvailable n u e)
  (h : fkIsingSquareNeighbor n u d hd = fkIsingSquareNeighbor n u e he) :
-- imply
  d = e := by
-- proof
  apply StatMech.Universality.fkIsingSquareNeighbor_injective n u d e hd he h

/--
[fkIsingSquareDirectionEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDirectionEdge_injective_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d e : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d)
  (he : fkIsingSquareDirectionAvailable n u e)
  (h : fkIsingSquareDirectionEdge n u d hd = fkIsingSquareDirectionEdge n u e he) :
-- imply
  d = e := by
-- proof
  apply StatMech.Universality.fkIsingSquareDirectionEdge_injective n u d e hd he h

/--
[fkIsingSquareBondMate_edge_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_edge_ne_eq
  {n : Nat}
  {x : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBondMate n hn x).1 ≠ x.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_edge_ne n hn x

/--
[fkIsingSquareBondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_ne_eq
  {n : Nat}
  {x : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBondMate n hn x ≠ x := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_ne n hn x

/--
[fkIsingSquareBondMate_cornerTurn_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_cornerTurn_ne_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareSideCorner (fkIsingSquareBondMate n hn d).2).2 ≠ (fkIsingSquareSideCorner d.2).2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_cornerTurn_ne n hn d

/--
[fkIsingSquareBondMate_ne_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_ne_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBondMate n hn x ≠ FKIsingMedialDart.localMate omega x := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_ne_localMate n hn omega x

/--
[fkIsingSquareOrientedEdge_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareOrientedEdge_source_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareOrientedEdge n (fkIsingSquareSourcePrimalEdge n hn) = fkIsingSquareSourceEdgeOrientation n hn := by
-- proof
  apply StatMech.Universality.fkIsingSquareOrientedEdge_source n hn

/--
[fkIsingSquareOrientedEdge_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareOrientedEdge_terminal_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareOrientedEdge n (fkIsingSquareTerminalPrimalEdge n hn) = fkIsingSquareTerminalEdgeOrientation n hn := by
-- proof
  apply StatMech.Universality.fkIsingSquareOrientedEdge_terminal n hn

/--
[fkIsingSquareMarkedA_ne_markedB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareMarkedA_ne_markedB_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareMarkedA n ≠ fkIsingSquareMarkedB n := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedA_ne_markedB n hn

/--
[fkIsingSquareMarkedA_not_adj_markedB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareMarkedA_not_adj_markedB_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  ¬(fkSquareBoxPlanar n).G.Adj (fkIsingSquareMarkedA n) (fkIsingSquareMarkedB n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareMarkedA_not_adj_markedB n hn

/--
[fkIsingSquare_source_ne_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_source_ne_terminal_eq
  {n : Nat} :
-- imply
  (FKIsingSquareMedialCarrier.source : FKIsingSquareMedialCarrier n) ≠ .terminal := by
-- proof
  apply StatMech.Universality.fkIsingSquare_source_ne_terminal n

/--
[fkIsingSquare_sourceAttachment_ne_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_sourceAttachment_ne_source_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareSourceAttachment n hn ≠ .source := by
-- proof
  apply StatMech.Universality.fkIsingSquare_sourceAttachment_ne_source n hn

/--
[fkIsingSquare_terminalAttachment_ne_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_terminalAttachment_ne_terminal_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareTerminalAttachment n hn ≠ .terminal := by
-- proof
  apply StatMech.Universality.fkIsingSquare_terminalAttachment_ne_terminal n hn

/--
[fkIsingSquareDartEndpoint_sourceAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDartEndpoint_sourceAttachment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareSourcePrimalEdge n hn, .west) = fkIsingSquareMarkedA n := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartEndpoint_sourceAttachment n hn

/--
[fkIsingSquareDartEndpoint_terminalAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDartEndpoint_terminalAttachment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareTerminalPrimalEdge n hn, .north) = fkIsingSquareMarkedB n := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartEndpoint_terminalAttachment n hn

/--
[fkIsingSquareSourceAttachment_ne_terminalAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareSourceAttachment_ne_terminalAttachment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareSourcePrimalEdge n hn, FKIsingMedialSide.west) ≠ (fkIsingSquareTerminalPrimalEdge n hn, FKIsingMedialSide.north) := by
-- proof
  apply StatMech.Universality.fkIsingSquareSourceAttachment_ne_terminalAttachment n hn

/--
[fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareSourcePrimalEdge n hn, .west) ≠ (fkIsingSquareTerminalPrimalEdge n hn, .north) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn

/--
[fkIsingSquareBondMate_sourceEdge_ne_terminalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareBondMate_sourceEdge_ne_terminalEdge_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBondMate n hn (fkIsingSquareSourcePrimalEdge n hn, .west)).1 ≠ (fkIsingSquareBondMate n hn (fkIsingSquareTerminalPrimalEdge n hn, .north)).1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareBondMate_sourceEdge_ne_terminalEdge n hn

/--
[fkIsingSquare_localMate_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_localMate_fst_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  (FKIsingMedialDart.localMate omega d).1 = d.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_localMate_fst n omega d

/--
[fkIsingSquare_localMate_cornerTurn_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_localMate_cornerTurn_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  (fkIsingSquareSideCorner (FKIsingMedialDart.localMate omega d).2).2 ≠ (fkIsingSquareSideCorner d.2).2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_localMate_cornerTurn_ne n omega d

/--
[fkIsingSquareCutBondMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCutBondMate_involutive_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Involutive (fkIsingSquareCutBondMate n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCutBondMate_involutive n hn

/--
[fkIsingSquareCutBondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCutBondMate_ne_eq
  {n : Nat}
  {x : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCutBondMate n hn x ≠ x := by
-- proof
  apply StatMech.Universality.fkIsingSquareCutBondMate_ne n hn x

/--
[fkIsingSquareCutBondMate_ne_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCutBondMate_ne_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCutBondMate n hn (.dart d) ≠ .dart (FKIsingMedialDart.localMate omega d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCutBondMate_ne_localMate n hn omega d

/--
[fkIsingSquareCutBondMate_dart_cornerTurn_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCutBondMate_dart_cornerTurn_ne_eq
  {n : Nat}
  {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareCutBondMate n hn (.dart d) = .dart f) :
-- imply
  (fkIsingSquareSideCorner f.2).2 ≠ (fkIsingSquareSideCorner d.2).2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareCutBondMate_dart_cornerTurn_ne n hn d f h

/--
[fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareLoopGraph n hn (setOpen e.1 omega) = medialTwoEdgeSwitch (fkIsingSquareLoopGraph n hn (setClosed e.1 omega)) (.dart (e, .west)) (.dart (e, .south)) (.dart (e, .east)) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e

/--
[fkIsingSquareCutBondMate_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCutBondMate_source_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCutBondMate n hn .source = .dart (fkIsingSquareSourceInteriorDart n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCutBondMate_source n hn

/--
[fkIsingSquareCutBondMate_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCutBondMate_terminal_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCutBondMate n hn .terminal = .dart (fkIsingSquareTerminalInteriorDart n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCutBondMate_terminal n hn

/--
[fkIsingSquareLoopGraph_source_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_source_adj_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).Adj .source (.dart (fkIsingSquareSourceInteriorDart n hn)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_source_adj n hn omega

/--
[fkIsingSquareLoopGraph_terminal_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_terminal_adj_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).Adj .terminal (.dart (fkIsingSquareTerminalInteriorDart n hn)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_terminal_adj n hn omega

/--
[fkIsingSquareLoopGraph_adj_source_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_adj_source_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).Adj .source z ↔ z = .dart (fkIsingSquareSourceInteriorDart n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_adj_source_iff n hn omega z

/--
[fkIsingSquareLoopGraph_adj_terminal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_adj_terminal_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).Adj .terminal z ↔ z = .dart (fkIsingSquareTerminalInteriorDart n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_adj_terminal_iff n hn omega z

/--
[fkIsingSquareLoopGraph_adj_dart_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_adj_dart_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).Adj (.dart d) z ↔ z = .dart (FKIsingMedialDart.localMate omega d) ∨ z = fkIsingSquareCutBondMate n hn (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_adj_dart_iff n hn omega d z

/--
[fkIsingSquareLocalSmoothingGraph_adj_dart_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLocalSmoothingGraph_adj_dart_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {z : FKIsingSquareMedialCarrier n} :
-- imply
  (fkIsingSquareLocalSmoothingGraph n omega).Adj (.dart d) z ↔ z = .dart (FKIsingMedialDart.localMate omega d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLocalSmoothingGraph_adj_dart_iff n omega d z

/--
[fkIsingSquareLoopGraph_isAlternating_localSmoothing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_isAlternating_localSmoothing_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).IsAlternating (fkIsingSquareLocalSmoothingGraph n omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_isAlternating_localSmoothing n hn omega

/--
[fkIsingSquareLoopGraph_adj_oddClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_adj_oddClass_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
-- imply
  fkIsingSquareCarrierOddClass n x ↔ ¬ fkIsingSquareCarrierOddClass n y := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_adj_oddClass n hn omega hxy

/--
[fkIsingSquareLoopGraph_source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_source_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).degree .source = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_source_degree n hn omega

/--
[fkIsingSquareLoopGraph_terminal_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_terminal_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).degree .terminal = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_terminal_degree n hn omega

/--
[fkIsingSquareLoopGraph_dart_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_dart_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).degree (.dart d) = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_dart_degree n hn omega d

/--
[fkIsingSquareLoopGraph_source_reachable_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLoopGraph_source_reachable_terminal_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareLoopGraph n hn omega).Reachable .source .terminal := by
-- proof
  apply StatMech.Universality.fkIsingSquareLoopGraph_source_reachable_terminal n hn omega

/--
[fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCompletedLoopGraph n hn (setOpen e.1 omega) = medialTwoEdgeSwitch (fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)) (.dart (e, .west)) (.dart (e, .south)) (.dart (e, .east)) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e

/--
[fkIsingSquareCompletedLoopGraph_reachable_source_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_reachable_source_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareCompletedLoopGraph n hn omega).Reachable .source z ↔ (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_reachable_source_iff n hn omega z

/--
[fkIsingSquareCompletedLoopGraph_source_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_source_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareCompletedLoopGraph n hn omega).degree .source = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_source_degree n hn omega

/--
[fkIsingSquareCompletedLoopGraph_terminal_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_terminal_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareCompletedLoopGraph n hn omega).degree .terminal = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega

/--
[fkIsingSquareCompletedLoopGraph_dart_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_dart_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareCompletedLoopGraph n hn omega).degree (.dart d) = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d

/--
[fkIsingSquareCompletedLoopGraph_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCompletedLoopGraph_even_degree_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  Even ((fkIsingSquareCompletedLoopGraph n hn omega).degree z) := by
-- proof
  apply StatMech.Universality.fkIsingSquareCompletedLoopGraph_even_degree n hn omega z

/--
[mem_fkIsingSquareExplorationFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma mem_fkIsingSquareExplorationFinset_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  z ∈ fkIsingSquareExplorationFinset n hn omega ↔ (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.mem_fkIsingSquareExplorationFinset_iff n hn omega z

/--
[fkIsingSquare_open_local_mem_of_closed_west_mem_not_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_local_mem_of_closed_west_mem_not_east_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
  (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
-- imply
  ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_local_mem_of_closed_west_mem_not_east n hn omega e hwest heast

/--
[fkIsingSquare_open_local_mem_of_closed_east_mem_not_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_local_mem_of_closed_east_mem_not_west_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
  (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
-- imply
  ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_local_mem_of_closed_east_mem_not_west n hn omega e heast hwest

/--
[fkIsingSquare_open_local_not_mem_of_closed_west_east_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_local_not_mem_of_closed_west_east_not_mem_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
  (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
-- imply
  ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_local_not_mem_of_closed_west_east_not_mem n hn omega e hwest heast

/--
[fkIsingSquare_local_switch_component_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_local_switch_component_classification_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧ ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨ ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧ ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨ ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧ ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨ ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧ (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_local_switch_component_classification n hn omega e

/--
[fkIsingSquare_source_mem_exploration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_source_mem_exploration_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (.source : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquare_source_mem_exploration n hn omega

/--
[fkIsingSquare_terminal_mem_exploration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_terminal_mem_exploration_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (.terminal : FKIsingSquareMedialCarrier n) ∈ fkIsingSquareExplorationFinset n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquare_terminal_mem_exploration n hn omega

/--
[fkIsingSquareExplorationOrder_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationOrder_nodup_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareExplorationOrder n hn omega).Nodup := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationOrder_nodup n hn omega

/--
[fkIsingSquareExplorationPath_oddClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationPath_oddClass_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hi : i ≤ (fkIsingSquareExplorationPath n hn omega : (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).length) :
-- imply
  fkIsingSquareCarrierOddClass n ((fkIsingSquareExplorationPath n hn omega : (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).getVert i) ↔ Odd i := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationPath_oddClass n hn omega i hi

/--
[fkIsingSquarePath_mem_support_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquarePath_mem_support_iff_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {p : (fkIsingSquareLoopGraph n hn omega).Walk (.source : FKIsingSquareMedialCarrier n) .terminal}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hp : p.IsPath) :
-- imply
  z ∈ p.support ↔ (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.fkIsingSquarePath_mem_support_iff_reachable n hn omega p hp z

/--
[mem_fkIsingSquareExplorationOrder_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma mem_fkIsingSquareExplorationOrder_iff_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  z ∈ fkIsingSquareExplorationOrder n hn omega ↔ (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
-- proof
  apply StatMech.Universality.mem_fkIsingSquareExplorationOrder_iff_reachable n hn omega z

/--
[mem_fkIsingSquareExplorationOrder_iff_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma mem_fkIsingSquareExplorationOrder_iff_finset_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  z ∈ fkIsingSquareExplorationOrder n hn omega ↔ z ∈ fkIsingSquareExplorationFinset n hn omega := by
-- proof
  apply StatMech.Universality.mem_fkIsingSquareExplorationOrder_iff_finset n hn omega z

/--
[fkIsingSquareExplorationPath_mem_edges_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationPath_mem_edges_of_adj_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hx : x ∈ fkIsingSquareExplorationOrder n hn omega)
  (hadj : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
-- imply
  s(x, y) ∈ (fkIsingSquareExplorationPath n hn omega : (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationPath_mem_edges_of_adj n hn omega hx hadj

/--
[idxOf_succ_of_pair_infix_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma idxOf_succ_of_pair_infix_nodup_eq
  [DecidableEq alpha]
  {x y : alpha}
  {l : List alpha}
-- given
  (hl : l.Nodup)
  (hxy : [x, y] <:+: l) :
-- imply
  l.idxOf y = l.idxOf x + 1 := by
-- proof
  apply StatMech.Universality.idxOf_succ_of_pair_infix_nodup hl hxy

/--
[isAlternating_path_edge_iff_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma isAlternating_path_edge_iff_odd_eq
  {G M : SimpleGraph V}
  {u v : V}
  {p : G.Walk u v}
-- given
  (halt : G.IsAlternating M)
  (hp : p.IsPath)
  (hfirst : ¬ M.Adj (p.getVert 0) (p.getVert 1)) :
-- imply
  ∀ i, i < p.length -> (M.Adj (p.getVert i) (p.getVert (i + 1)) ↔ Odd i) := by
-- proof
  apply StatMech.Universality.isAlternating_path_edge_iff_odd halt p hp hfirst

/--
[fkIsingSquare_localMate_infix_explorationOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_localMate_infix_explorationOrder_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
-- imply
  [(.dart (e, side) : FKIsingSquareMedialCarrier n), .dart (FKIsingMedialDart.localMate omega (e, side))] <:+: fkIsingSquareExplorationOrder n hn omega ∨ [(.dart (FKIsingMedialDart.localMate omega (e, side)) : FKIsingSquareMedialCarrier n), .dart (e, side)] <:+: fkIsingSquareExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquare_localMate_infix_explorationOrder n hn omega e side h

/--
[fkIsingSquare_localMate_idxOf_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_localMate_idxOf_adjacent_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
-- imply
  (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (FKIsingMedialDart.localMate omega (e, side))) = (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (e, side)) + 1 ∨ (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (e, side)) = (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (FKIsingMedialDart.localMate omega (e, side))) + 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_localMate_idxOf_adjacent n hn omega e side h

/--
[fkIsingSquare_localMate_infix_of_counterclockwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_localMate_infix_of_counterclockwise_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hccw : (fkIsingSquareSideCorner side).2 = .counterclockwise)
  (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
-- imply
  [(.dart (e, side) : FKIsingSquareMedialCarrier n), .dart (FKIsingMedialDart.localMate omega (e, side))] <:+: fkIsingSquareExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquare_localMate_infix_of_counterclockwise n hn omega e side hccw h

/--
[fkIsingSquare_open_pathUses_west_iff_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_pathUses_west_iff_north_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ↔ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_pathUses_west_iff_north n hn omega e

/--
[fkIsingSquare_open_pathUses_east_iff_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_pathUses_east_iff_south_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ↔ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_pathUses_east_iff_south n hn omega e

/--
[fkIsingSquare_closed_pathUses_west_iff_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_pathUses_west_iff_south_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ↔ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .south := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_pathUses_west_iff_south n hn omega e

/--
[fkIsingSquare_closed_pathUses_east_iff_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_pathUses_east_iff_north_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ↔ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .north := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_pathUses_east_iff_north n hn omega e

/--
[walkSplice_of_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma walkSplice_of_order_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v a b c d : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath)
  (ha : a ∈ p.support)
  (hb : b ∈ p.support)
  (hc : c ∈ p.support)
  (hd : d ∈ p.support)
  (hab : p.support.idxOf a < p.support.idxOf b)
  (hbc : p.support.idxOf b < p.support.idxOf c)
  (hcd : p.support.idxOf c < p.support.idxOf d) :
-- imply
  ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v, q.IsPath ∧ q.support = p.support.take (p.support.idxOf a + 1) ++ p.support.drop (p.support.idxOf d) := by
-- proof
  apply StatMech.Universality.walkSplice_of_order G p hp ha hb hc hd hab hbc hcd

/--
[walkSplice_membership_of_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma walkSplice_membership_of_order_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v a b c d : V}
  {p : G.Walk u v}
-- given
  (hp : p.IsPath)
  (ha : a ∈ p.support)
  (hb : b ∈ p.support)
  (hc : c ∈ p.support)
  (hd : d ∈ p.support)
  (hab : p.support.idxOf a < p.support.idxOf b)
  (hbc : p.support.idxOf b < p.support.idxOf c)
  (hcd : p.support.idxOf c < p.support.idxOf d) :
-- imply
  ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v, q.IsPath ∧ q.support = p.support.take (p.support.idxOf a + 1) ++ p.support.drop (p.support.idxOf d) ∧ a ∈ q.support ∧ d ∈ q.support ∧ b ∉ q.support ∧ c ∉ q.support := by
-- proof
  apply StatMech.Universality.walkSplice_membership_of_order G p hp ha hb hc hd hab hbc hcd

/--
[fkIsingSquare_closed_west_south_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_west_south_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  [(.dart (e, .west) : FKIsingSquareMedialCarrier n), .dart (e, .south)] <:+: fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_west_south_oriented_infix n hn omega e h

/--
[fkIsingSquare_closed_east_north_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_east_north_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  [(.dart (e, .east) : FKIsingSquareMedialCarrier n), .dart (e, .north)] <:+: fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_east_north_oriented_infix n hn omega e h

/--
[fkIsingSquare_open_west_north_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_west_north_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  [(.dart (e, .west) : FKIsingSquareMedialCarrier n), .dart (e, .north)] <:+: fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_west_north_oriented_infix n hn omega e h

/--
[fkIsingSquare_open_east_south_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_east_south_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  [(.dart (e, .east) : FKIsingSquareMedialCarrier n), .dart (e, .south)] <:+: fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_east_south_oriented_infix n hn omega e h

/--
[fkIsingSquare_double_visit_closed_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_closed_order_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  let p := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) p.idxOf (.dart (e, .south)) < p.idxOf (.dart (e, .east)) ∨ p.idxOf (.dart (e, .north)) < p.idxOf (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_closed_order n hn omega e hwest heast

/--
[fkIsingSquare_double_visit_open_pair_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_open_pair_classification_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (_hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (_heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨ (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨ (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨ (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_open_pair_classification n hn omega e _hwest _heast

/--
[fkIsingSquare_double_visit_open_pair_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_open_pair_exact_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨ (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_open_pair_exact n hn omega e hwest heast

/--
[fkIsingSquare_local_switch_path_membership_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_local_switch_path_membership_classification_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧ ∀ side, ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e side) ∨ (fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧ ∀ side, fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e side) ∨ (¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧ ∀ side, fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e side) ∨ (fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_local_switch_path_membership_classification n hn omega e

/--
[fkIsingSquareDartDirection_sourceInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDartDirection_sourceInterior_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDartDirection n (fkIsingSquareSourcePrimalEdge n hn, .west) = .east := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartDirection_sourceInterior n hn

/--
[fkIsingSquareDartDirection_terminalInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareDartDirection_terminalInterior_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDartDirection n (fkIsingSquareTerminalPrimalEdge n hn, .north) = .south := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartDirection_terminalInterior n hn

/--
[fkIsingSquareCarrierTangentCode_exteriorCutStart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCarrierTangentCode_exteriorCutStart_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCarrierTangentCode n hn (.dart (fkIsingSquareExteriorCutStart n hn)) = 7 := by
-- proof
  apply StatMech.Universality.fkIsingSquareCarrierTangentCode_exteriorCutStart n hn

/--
[fkIsingSquareCarrierTangentCode_exteriorCutEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareCarrierTangentCode_exteriorCutEnd_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareCarrierTangentCode n hn (.dart (fkIsingSquareExteriorCutEnd n hn)) = 3 := by
-- proof
  apply StatMech.Universality.fkIsingSquareCarrierTangentCode_exteriorCutEnd n hn

/--
[fkIsingSquareExteriorCutTurn_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExteriorCutTurn_forward_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareExteriorCutTurn n hn (fkIsingSquareExteriorCutStart n hn) (fkIsingSquareExteriorCutEnd n hn) = 8 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExteriorCutTurn_forward n hn

/--
[fkIsingSquareExteriorCutTurn_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExteriorCutTurn_reverse_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareExteriorCutTurn n hn (fkIsingSquareExteriorCutEnd n hn) (fkIsingSquareExteriorCutStart n hn) = -8 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExteriorCutTurn_reverse n hn

/--
[fkIsingSquareExteriorCutTurn_forward_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExteriorCutTurn_forward_unique_eq
  {z : Int}
-- given
  (hzmod : z % 8 = 0)
  (hzlo : 4 < z)
  (hzhi : z ≤ 12) :
-- imply
  z = 8 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExteriorCutTurn_forward_unique z hzmod hzlo hzhi

/--
[fkIsingSquareExteriorCutTurn_reverse_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExteriorCutTurn_reverse_unique_eq
  {z : Int}
-- given
  (hzmod : z % 8 = 0)
  (hzlo : -12 ≤ z)
  (hzhi : z < -4) :
-- imply
  z = -8 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExteriorCutTurn_reverse_unique z hzmod hzlo hzhi

/--
[fkIsingSquareExteriorCut_principal_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExteriorCut_principal_forward_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareSignedEighthTurn (fkIsingSquareCarrierTangentCode n hn (.dart (fkIsingSquareExteriorCutStart n hn))) (fkIsingSquareCarrierTangentCode n hn (.dart (fkIsingSquareExteriorCutEnd n hn)) + 4) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExteriorCut_principal_forward n hn

/--
[fkIsingSquareExteriorCut_principal_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExteriorCut_principal_reverse_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareSignedEighthTurn (fkIsingSquareCarrierTangentCode n hn (.dart (fkIsingSquareExteriorCutEnd n hn))) (fkIsingSquareCarrierTangentCode n hn (.dart (fkIsingSquareExteriorCutStart n hn)) + 4) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExteriorCut_principal_reverse n hn

/--
[fkIsingSquareExplorationTransitionTurn_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationTransitionTurn_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareExplorationTransitionTurn n hn omega (.dart d) (.dart (FKIsingMedialDart.localMate omega d)) = fkIsingSquareSignedEighthTurn (fkIsingSquareCarrierTangentCode n hn (.dart d) + 4) (fkIsingSquareCarrierTangentCode n hn (.dart (FKIsingMedialDart.localMate omega d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationTransitionTurn_localMate n hn omega d

/--
[fkIsingSquareExplorationTransitionTurn_bond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationTransitionTurn_bond_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : f ≠ FKIsingMedialDart.localMate omega d) :
-- imply
  fkIsingSquareExplorationTransitionTurn n hn omega (.dart d) (.dart f) = fkIsingSquareSignedEighthTurn (fkIsingSquareCarrierTangentCode n hn (.dart d)) (fkIsingSquareCarrierTangentCode n hn (.dart f) + 4) + fkIsingSquareExteriorCutTurn n hn d f := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationTransitionTurn_bond n hn omega d f h

/--
[fkIsingSquareExplorationTransitionTurn_exterior_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationTransitionTurn_exterior_forward_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareExteriorCutEnd n hn ≠ FKIsingMedialDart.localMate omega (fkIsingSquareExteriorCutStart n hn)) :
-- imply
  fkIsingSquareExplorationTransitionTurn n hn omega (.dart (fkIsingSquareExteriorCutStart n hn)) (.dart (fkIsingSquareExteriorCutEnd n hn)) = 8 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationTransitionTurn_exterior_forward n hn omega h

/--
[fkIsingSquareExplorationTransitionTurn_exterior_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationTransitionTurn_exterior_reverse_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareExteriorCutStart n hn ≠ FKIsingMedialDart.localMate omega (fkIsingSquareExteriorCutEnd n hn)) :
-- imply
  fkIsingSquareExplorationTransitionTurn n hn omega (.dart (fkIsingSquareExteriorCutEnd n hn)) (.dart (fkIsingSquareExteriorCutStart n hn)) = -8 := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationTransitionTurn_exterior_reverse n hn omega h

/--
[fkIsingSquareExplorationTransitionTurn_local_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareExplorationTransitionTurn_local_table_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .west)) (.dart (e, .south)) = -2) ∧ (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .south)) (.dart (e, .west)) = 2) ∧ (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .east)) (.dart (e, .north)) = -2) ∧ (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .north)) (.dart (e, .east)) = 2) ∧ (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .west)) (.dart (e, .north)) = 2) ∧ (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .north)) (.dart (e, .west)) = -2) ∧ (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .east)) (.dart (e, .south)) = 2) ∧ (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .south)) (.dart (e, .east)) = -2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationTransitionTurn_local_table n hn omega e

/--
[fkIsingSquareLiftedTurnCount_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLiftedTurnCount_succ_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hi : i + 1 < (fkIsingSquareExplorationOrder n hn omega).length) :
-- imply
  fkIsingSquareLiftedTurnCount n hn omega (fkIsingSquareExplorationOrder n hn omega)[i + 1] = fkIsingSquareLiftedTurnCount n hn omega (fkIsingSquareExplorationOrder n hn omega)[i] + fkIsingSquareExplorationTransitionTurn n hn omega (fkIsingSquareExplorationOrder n hn omega)[i] (fkIsingSquareExplorationOrder n hn omega)[i + 1] := by
-- proof
  apply StatMech.Universality.fkIsingSquareLiftedTurnCount_succ n hn omega i hi

/--
[fkIsingSquareLiftedTurnCount_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLiftedTurnCount_localMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
-- imply
  (fkIsingSquareLiftedTurnCount n hn omega (.dart (FKIsingMedialDart.localMate omega (e, side))) = fkIsingSquareLiftedTurnCount n hn omega (.dart (e, side)) + fkIsingSquareExplorationTransitionTurn n hn omega (.dart (e, side)) (.dart (FKIsingMedialDart.localMate omega (e, side)))) ∨ (fkIsingSquareLiftedTurnCount n hn omega (.dart (e, side)) = fkIsingSquareLiftedTurnCount n hn omega (.dart (FKIsingMedialDart.localMate omega (e, side))) + fkIsingSquareExplorationTransitionTurn n hn omega (.dart (FKIsingMedialDart.localMate omega (e, side))) (.dart (e, side))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLiftedTurnCount_localMate n hn omega e side h

/--
[fkIsingSquare_closed_west_south_turnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_west_south_turnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega) (.dart (e, .south)) = fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega) (.dart (e, .west)) - 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_west_south_turnCount n hn omega e h

/--
[fkIsingSquare_closed_east_north_turnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_east_north_turnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega) (.dart (e, .north)) = fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega) (.dart (e, .east)) - 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_east_north_turnCount n hn omega e h

/--
[fkIsingSquare_open_west_north_turnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_west_north_turnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega) (.dart (e, .north)) = fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega) (.dart (e, .west)) + 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_west_north_turnCount n hn omega e h

/--
[fkIsingSquare_open_east_south_turnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_east_south_turnCount_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega) (.dart (e, .south)) = fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega) (.dart (e, .east)) + 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_east_south_turnCount n hn omega e h

/--
[fkIsingSquarePhysicalTransitionTurn_local_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquarePhysicalTransitionTurn_local_table_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .west)) (.dart (e, .south)) = -2) ∧ (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .south)) (.dart (e, .west)) = 2) ∧ (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .east)) (.dart (e, .north)) = -2) ∧ (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .north)) (.dart (e, .east)) = 2) ∧ (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .west)) (.dart (e, .north)) = 2) ∧ (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .north)) (.dart (e, .west)) = -2) ∧ (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .east)) (.dart (e, .south)) = 2) ∧ (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega) (.dart (e, .south)) (.dart (e, .east)) = -2) := by
-- proof
  apply StatMech.Universality.fkIsingSquarePhysicalTransitionTurn_local_table n hn omega e

/--
[fkIsingSquareLiftedWinding_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLiftedWinding_succ_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hi : i + 1 < (fkIsingSquareExplorationOrder n hn omega).length) :
-- imply
  fkIsingSquareLiftedWinding n hn omega (fkIsingSquareExplorationOrder n hn omega)[i + 1] = fkIsingSquareLiftedWinding n hn omega (fkIsingSquareExplorationOrder n hn omega)[i] + (fkIsingSquarePhysicalTransitionTurn n hn omega (fkIsingSquareExplorationOrder n hn omega)[i] (fkIsingSquareExplorationOrder n hn omega)[i + 1] : Real) * (Real.pi / 4) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLiftedWinding_succ n hn omega i hi

/--
[fkIsingSquareLiftedWinding_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquareLiftedWinding_terminal_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareLiftedWinding n hn omega .terminal = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareLiftedWinding_terminal n hn omega

/--
[fkIsingSquare_closed_west_south_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_west_south_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  fkIsingSquareLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .south)) = fkIsingSquareLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .west)) - Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_west_south_winding n hn omega e h

/--
[fkIsingSquare_closed_east_north_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_closed_east_north_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  fkIsingSquareLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .north)) = fkIsingSquareLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .east)) - Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_closed_east_north_winding n hn omega e h

/--
[fkIsingSquare_open_west_north_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_west_north_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  fkIsingSquareLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .north)) = fkIsingSquareLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .west)) + Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_west_north_winding n hn omega e h

/--
[fkIsingSquare_open_east_south_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean)
-/
@[path]
private lemma fkIsingSquare_open_east_south_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  fkIsingSquareLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .south)) = fkIsingSquareLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .east)) + Real.pi / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquare_open_east_south_winding n hn omega e h


-- created on 2026-10-23
