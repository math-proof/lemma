import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part34
open StatMech StatMech.Universality


/--
[fkIsingSquareWiredUnitDiagonalStep_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalStep_injective_eq :
-- imply
  Function.Injective fkIsingSquareWiredUnitDiagonalStep := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalStep_injective

/--
[fkIsingSquareWiredUnitDiagonalStep_add_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalStep_add_reverse_eq
  {a : Fin 4} :
-- imply
  fkIsingSquareWiredUnitDiagonalStep a + fkIsingSquareWiredUnitDiagonalStep (fkIsingSquareWiredUnitDiagonalReverse a) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalStep_add_reverse a

/--
[fkIsingSquareWiredIntPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredIntPoint_injective_eq :
-- imply
  Function.Injective fkIsingSquareWiredIntPoint := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIntPoint_injective

/--
[fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal_eq
  {p q : Int × Int}
  {a : Fin 4} :
-- imply
  ¬Sbtw Real (fkIsingSquareWiredIntPoint p) (fkIsingSquareWiredIntPoint q) (fkIsingSquareWiredIntPoint (p + fkIsingSquareWiredUnitDiagonalStep a)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal p q a

/--
[fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq_eq
  {p q : Int × Int}
  {a b : Fin 4}
  {z : Complex}
-- given
  (hp : Sbtw Real (fkIsingSquareWiredIntPoint p) z (fkIsingSquareWiredIntPoint (p + fkIsingSquareWiredUnitDiagonalStep a)))
  (hq : Sbtw Real (fkIsingSquareWiredIntPoint q) z (fkIsingSquareWiredIntPoint (q + fkIsingSquareWiredUnitDiagonalStep b))) :
-- imply
  p + (p + fkIsingSquareWiredUnitDiagonalStep a) = q + (q + fkIsingSquareWiredUnitDiagonalStep b) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq p q a b z hp hq

/--
[fkIsingSquareWired_cycle_turn_mod_sixteen_of_simplePolygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_cycle_turn_mod_sixteen_of_simplePolygon_eq
  {m : Nat}
  [NeZero m]
  {polygon : StatMech.FrontierA.KWFiniteSimplePolygon m}
  {turn : Int}
-- given
  (hphase : Complex.exp (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) = StatMech.FrontierA.kwVectorPhaseCycle polygon.edgeList) :
-- imply
  turn ≡ 8 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_cycle_turn_mod_sixteen_of_simplePolygon polygon turn hphase

/--
[fkIsingSquareWiredPortIntPosition_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortIntPosition_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareWiredPortIntPosition n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortIntPosition_injective n

/--
[fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  ∃ a : Fin 4, fkIsingSquareWiredPortIntPosition n (FKIsingMedialDart.localMate omega d) = fkIsingSquareWiredPortIntPosition n d + fkIsingSquareWiredUnitDiagonalStep a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal n omega d

/--
[fkIsingSquareWiredPortIntPosition_directionDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortIntPosition_directionDart_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  fkIsingSquareWiredPortIntPosition n (fkIsingSquareDirectionDart n u d hd turn) = (4 * u.1 0, 4 * u.1 1) + fkIsingSquareWiredPortOffset d turn := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortIntPosition_directionDart n u d hd turn

/--
[fkIsingSquareWiredPortSlot_direction_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortSlot_direction_turn_eq
  {i : Fin 8} :
-- imply
  fkIsingSquareWiredPortSlot (fkIsingSquareWiredPortSlotDirection i) (fkIsingSquareWiredPortSlotTurn i) = i := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortSlot_direction_turn i

/--
[fkIsingSquareWiredPortSlotDirection_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortSlotDirection_slot_eq
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn} :
-- imply
  fkIsingSquareWiredPortSlotDirection (fkIsingSquareWiredPortSlot d turn) = d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortSlotDirection_slot d turn

/--
[fkIsingSquareWiredPortSlotTurn_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortSlotTurn_slot_eq
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn} :
-- imply
  fkIsingSquareWiredPortSlotTurn (fkIsingSquareWiredPortSlot d turn) = turn := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortSlotTurn_slot d turn

/--
[fkIsingSquareWiredPortOctagonOffset_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortOctagonOffset_slot_eq
  {d : FKIsingSquareDirection}
  {turn : FKIsingSquareCornerTurn} :
-- imply
  fkIsingSquareWiredPortOctagonOffset (fkIsingSquareWiredPortSlot d turn) = fkIsingSquareWiredPortOffset d turn := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortOctagonOffset_slot d turn

/--
[fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal_eq
  {i : Fin 8} :
-- imply
  ∃ a : Fin 4, fkIsingSquareWiredPortOctagonOffset (i + 1) = fkIsingSquareWiredPortOctagonOffset i + fkIsingSquareWiredUnitDiagonalStep a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal i

/--
[fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection} :
-- imply
  fkIsingSquareWiredBondArcLength n u d = 1 ∨ fkIsingSquareWiredBondArcLength n u d = 3 ∨ fkIsingSquareWiredBondArcLength n u d = 5 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d

/--
[fkIsingSquareWiredPortSlot_nextDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortSlot_nextDirection_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection} :
-- imply
  fkIsingSquareWiredPortSlot (fkIsingSquareNextDirection n u d) .clockwise = fkIsingSquareWiredPortSlot d .counterclockwise + fkIsingSquareWiredBondArcLength n u d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortSlot_nextDirection n u d

/--
[fkIsingSquareWiredSlotIntPosition_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotIntPosition_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareWiredSlotIntPosition n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotIntPosition_injective n

/--
[fkIsingSquareWiredDartSlot_dartOfSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredDartSlot_dartOfSlot_eq
  {n : Nat}
  {x : (fkSquareBoxPlanar n).V × Fin 8}
-- given
  (h : fkIsingSquareWiredSlotAvailable n x) :
-- imply
  fkIsingSquareWiredDartSlot n (fkIsingSquareWiredDartOfSlot n x h) = x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDartSlot_dartOfSlot n x h

/--
[fkIsingSquareWiredDartOfSlot_dartSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredDartOfSlot_dartSlot_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWiredDartOfSlot n (fkIsingSquareWiredDartSlot n d) (by simpa [fkIsingSquareWiredSlotAvailable, fkIsingSquareWiredDartSlot] using fkIsingSquareDartDirection_available n d) = d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDartOfSlot_dartSlot n d

/--
[fkIsingSquareWiredSlotIntPosition_dartSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotIntPosition_dartSlot_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) = fkIsingSquareWiredPortIntPosition n d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotIntPosition_dartSlot n d

/--
[fkIsingSquareWiredDartSlot_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredDartSlot_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareWiredDartSlot n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDartSlot_injective n

/--
[fkIsingSquareWiredSlotRingMidpoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingMidpoint_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fun x : (fkSquareBoxPlanar n).V × Fin 8 => fkIsingSquareWiredSlotIntPosition n x + fkIsingSquareWiredSlotIntPosition n (x.1, x.2 + 1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingMidpoint_injective n

/--
[fkIsingSquareWiredSlotRingGraph_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingGraph_step_eq
  {n : Nat}
  {x y : FKIsingSquareWiredSlotCarrier n}
-- given
  (h : (fkIsingSquareWiredSlotRingGraph n).Adj x y) :
-- imply
  ∃ a : Fin 4, fkIsingSquareWiredSlotIntPosition n y = fkIsingSquareWiredSlotIntPosition n x + fkIsingSquareWiredUnitDiagonalStep a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingGraph_step n h

/--
[fkIsingSquareWiredSlotRingGraph_adj_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingGraph_adj_succ_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {i : Fin 8}
-- given
  (hactive : fkIsingSquareWiredSlotRingActive n (u, i)) :
-- imply
  (fkIsingSquareWiredSlotRingGraph n).Adj (u, i) (u, i + 1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingGraph_adj_succ n u i hactive

/--
[fkIsingSquareWiredSlotRingGraph_reachable_nextDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingGraph_reachable_nextDirection_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  (fkIsingSquareWiredSlotRingGraph n).Reachable (u, fkIsingSquareWiredPortSlot d .counterclockwise) (u, fkIsingSquareWiredPortSlot (fkIsingSquareNextDirection n u d) .clockwise) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingGraph_reachable_nextDirection n hn u d hd

/--
[fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk (u, fkIsingSquareWiredPortSlot d .counterclockwise) (u, fkIsingSquareWiredPortSlot (fkIsingSquareNextDirection n u d) .clockwise), p.IsPath ∧ p.length = (fkIsingSquareWiredBondArcLength n u d).val := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection n hn u d hd

/--
[fkIsingSquareWiredSlotRingGraph_reachable_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingGraph_reachable_bondMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredSlotRingGraph n).Reachable (fkIsingSquareWiredDartSlot n d) (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingGraph_reachable_bondMate n hn d

/--
[fkIsingSquareWiredSlotRingGraph_exists_path_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingGraph_exists_path_bondMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk (fkIsingSquareWiredDartSlot n d) (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)), p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingGraph_exists_path_bondMate n hn d

/--
[fkIsingSquareWiredSlotLocalGraph_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotLocalGraph_step_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredSlotCarrier n}
-- given
  (h : (fkIsingSquareWiredSlotLocalGraph n omega).Adj x y) :
-- imply
  ∃ a : Fin 4, fkIsingSquareWiredSlotIntPosition n y = fkIsingSquareWiredSlotIntPosition n x + fkIsingSquareWiredUnitDiagonalStep a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotLocalGraph_step n omega h

/--
[fkIsingSquareWiredSlotLocalEdge_eq_of_midpoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotLocalEdge_eq_of_midpoint_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hmid : fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) + fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega d)) = fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n f) + fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega f))) :
-- imply
  s(fkIsingSquareWiredDartSlot n d, fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega d)) = s(fkIsingSquareWiredDartSlot n f, fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega f)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotLocalEdge_eq_of_midpoint_eq n omega d f hmid

/--
[fkIsingSquareWiredSlotLocalRing_midpoint_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotLocalRing_midpoint_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {u : (fkSquareBoxPlanar n).V}
  {i : Fin 8}
-- given
  (hactive : fkIsingSquareWiredSlotRingActive n (u, i)) :
-- imply
  fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) + fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega d)) ≠ fkIsingSquareWiredSlotIntPosition n (u, i) + fkIsingSquareWiredSlotIntPosition n (u, i + 1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega d u i hactive

/--
[fkIsingSquareWiredExpandedIntPosition_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedIntPosition_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fkIsingSquareWiredExpandedIntPosition n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedIntPosition_injective n hn

/--
[fkIsingSquareWiredExpanded_bulge_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpanded_bulge_steps_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredExpandedIntPosition n hn (.inr k) = fkIsingSquareWiredExpandedIntPosition n hn (fkIsingSquareWiredExpandedStart n hn k) + fkIsingSquareWiredUnitDiagonalStep 1) ∧ (fkIsingSquareWiredExpandedIntPosition n hn (fkIsingSquareWiredExpandedMiddle n hn k) = fkIsingSquareWiredExpandedIntPosition n hn (.inr k) + fkIsingSquareWiredUnitDiagonalStep 3) ∧ (fkIsingSquareWiredExpandedIntPosition n hn (fkIsingSquareWiredExpandedEnd n hn k) = fkIsingSquareWiredExpandedIntPosition n hn (fkIsingSquareWiredExpandedMiddle n hn k) + fkIsingSquareWiredUnitDiagonalStep 2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpanded_bulge_steps n hn k

/--
[fkIsingSquareWiredExpandedBulgeMidpoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedBulgeMidpoint_injective_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Injective (fun x : Fin (2 * n) × Fin 3 => fkIsingSquareWiredExpandedBulgeMidpoint n hn x.1 x.2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedBulgeMidpoint_injective n hn

/--
[fkIsingSquareWiredSlotLocalBulge_midpoint_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotLocalBulge_midpoint_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Fin (2 * n)}
  {j : Fin 3}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) + fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega d)) ≠ fkIsingSquareWiredExpandedBulgeMidpoint n hn k j := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotLocalBulge_midpoint_ne n hn omega d k j

/--
[fkIsingSquareWiredSlotRingBulge_midpoint_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingBulge_midpoint_ne_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {i : Fin 8}
  {k : Fin (2 * n)}
  {j : Fin 3}
-- given
  (hn : 0 < n)
  (hkeep : ¬fkIsingSquareWiredLeftRingRemoved n (u, i)) :
-- imply
  fkIsingSquareWiredSlotIntPosition n (u, i) + fkIsingSquareWiredSlotIntPosition n (u, i + 1) ≠ fkIsingSquareWiredExpandedBulgeMidpoint n hn k j := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingBulge_midpoint_ne n hn u i hkeep k j

/--
[fkIsingSquareWiredExpandedAdj_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedAdj_symm_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  Symmetric (fkIsingSquareWiredExpandedAdj n hn omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedAdj_symm n hn omega

/--
[fkIsingSquareWiredExpandedAdj_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedAdj_irrefl_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  Irreflexive (fkIsingSquareWiredExpandedAdj n hn omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedAdj_irrefl n hn omega

/--
[fkIsingSquareWiredUnitDiagonal_step_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonal_step_reverse_eq
  {p q : Int × Int}
  {a : Fin 4}
-- given
  (h : q = p + fkIsingSquareWiredUnitDiagonalStep a) :
-- imply
  ∃ b : Fin 4, p = q + fkIsingSquareWiredUnitDiagonalStep b := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonal_step_reverse p q a h

/--
[fkIsingSquareWiredExpandedGraph_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_step_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredExpandedCarrier n}
-- given
  (hn : 0 < n)
  (h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj x y) :
-- imply
  ∃ a : Fin 4, fkIsingSquareWiredExpandedIntPosition n hn y = fkIsingSquareWiredExpandedIntPosition n hn x + fkIsingSquareWiredUnitDiagonalStep a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_step n hn omega h

/--
[fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
-- imply
  (fkIsingSquareWiredExpandedGraph n hn omega).Reachable (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left n hn omega d hleft

/--
[fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))), p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left n hn omega d hleft

/--
[fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {localDart d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))), p.IsPath ∧ s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local n hn omega localDart d hleft

/--
[fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
  (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  ∃ a b : FKIsingSquareWiredSlotCarrier n, fkIsingSquareWiredDartSlot n d = a ∧ fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d) = b ∧ ¬fkIsingSquareWiredLeftRingRemoved n a ∧ ¬fkIsingSquareWiredLeftRingRemoved n b ∧ (fkIsingSquareWiredSlotRingGraph n).Adj a b := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary n hn omega d hleft hclockwise hboundary

/--
[fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
  (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  (fkIsingSquareWiredExpandedGraph n hn omega).Adj (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary n hn omega d hleft hclockwise hboundary

/--
[fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {localDart d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
  (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))), p.IsPath ∧ s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local n hn omega localDart d hleft hclockwise hboundary

/--
[fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
  (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  (fkIsingSquareWiredExpandedGraph n hn omega).Reachable (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary n hn omega d hleft hclockwise hboundary

/--
[fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hd : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary n hn d hd

/--
[fkIsingSquareWiredExpandedGraph_reachable_bulge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_reachable_bulge_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredExpandedGraph n hn omega).Reachable (fkIsingSquareWiredExpandedStart n hn k) (fkIsingSquareWiredExpandedEnd n hn k) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_reachable_bulge n hn omega k

/--
[fkIsingSquareWiredExpandedGraph_exists_path_bulge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_path_bulge_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (fkIsingSquareWiredExpandedStart n hn k) (fkIsingSquareWiredExpandedEnd n hn k), p.IsPath ∧ p.length = 3 ∧ p.support = [fkIsingSquareWiredExpandedStart n hn k, .inr k, fkIsingSquareWiredExpandedMiddle n hn k, fkIsingSquareWiredExpandedEnd n hn k] ∧ p.edges = [fkIsingSquareWiredExpandedBulgeEdge n hn k 0, fkIsingSquareWiredExpandedBulgeEdge n hn k 1, fkIsingSquareWiredExpandedBulgeEdge n hn k 2] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_path_bulge n hn omega k

/--
[fkIsingSquareWiredExpandedGraph_exists_path_bulge_avoids_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_path_bulge_avoids_local_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {localDart : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (fkIsingSquareWiredExpandedStart n hn k) (fkIsingSquareWiredExpandedEnd n hn k), p.IsPath ∧ s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_path_bulge_avoids_local n hn omega localDart k

/--
[fkIsingSquareWiredExpandedGraph_edge_eq_of_midpoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_edge_eq_of_midpoint_eq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y z w : FKIsingSquareWiredExpandedCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredExpandedGraph n hn omega).Adj x y)
  (hzw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj z w)
  (hmid : fkIsingSquareWiredExpandedIntPosition n hn x + fkIsingSquareWiredExpandedIntPosition n hn y = fkIsingSquareWiredExpandedIntPosition n hn z + fkIsingSquareWiredExpandedIntPosition n hn w) :
-- imply
  s(x, y) = s(z, w) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_edge_eq_of_midpoint_eq n hn omega hxy hzw hmid

/--
[fkIsingSquareWiredExpandedCyclePhaseSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedCyclePhaseSign_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  StatMech.FrontierA.KWStraightLineCyclePhaseSign (fkIsingSquareWiredExpandedGraph n hn omega) (fkIsingSquareWiredExpandedEmbedding n hn omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedCyclePhaseSign n hn omega

/--
[fkIsingSquareWiredExpandedCycle_phase_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedCycle_phase_eq_neg_one_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {root : FKIsingSquareWiredExpandedCarrier n}
  {p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root}
-- given
  (hn : 0 < n)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ StatMech.FrontierA.kwLoopPhaseProduct (fkIsingSquareWiredExpandedEmbedding n hn omega).turnPhase (StatMech.FrontierA.kwGraphCycleDartLoop p) = -1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedCycle_phase_eq_neg_one n hn omega p hp

/--
[fkIsingSquareWiredExpandedCycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedCycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {root : FKIsingSquareWiredExpandedCarrier n}
  {p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root}
  {turn : Int}
-- given
  (hn : 0 < n)
  (hp : p.IsCycle)
  (hphase : letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ Complex.exp (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) = StatMech.FrontierA.kwLoopPhaseProduct (fkIsingSquareWiredExpandedEmbedding n hn omega).turnPhase (StatMech.FrontierA.kwGraphCycleDartLoop p)) :
-- imply
  turn ≡ 8 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedCycle_turn_mod_sixteen n hn omega p hp turn hphase

/--
[fkIsingSquareWired_one_visit_west_carrierCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_carrierCycle_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)), s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk (.dart (e, .east)) (.dart (e, .north))}
-- given
  (hn : 0 < n)
  (hr : r.IsPath) :
-- imply
  ∃ p : (fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).Walk (.dart (e, .east)) (.dart (e, .east)), p.IsCycle ∧ p.support = (.dart (e, .east) : FKIsingSquareWiredCarrier n) :: r.reverse.support := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_carrierCycle n hn omega e r hr

/--
[fkIsingSquareWired_one_visit_east_carrierCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_carrierCycle_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)), s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk (.dart (e, .west)) (.dart (e, .south))}
-- given
  (hn : 0 < n)
  (hr : r.IsPath) :
-- imply
  ∃ p : (fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).Walk (.dart (e, .west)) (.dart (e, .west)), p.IsCycle ∧ p.support = (.dart (e, .west) : FKIsingSquareWiredCarrier n) :: r.reverse.support := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_carrierCycle n hn omega e r hr

/--
[fkIsingSquareWiredPhysicalBlackOfDart_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPhysicalBlackOfDart_bijective_eq
  {n : Nat} :
-- imply
  Function.Bijective (fkIsingSquareWiredPhysicalBlackOfDart n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPhysicalBlackOfDart_bijective n

/--
[fkIsingSquareWiredBlackOfDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackOfDart_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareWiredBlackOfDart n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackOfDart_injective n

/--
[fkIsingSquareWiredPhysicalBlackPortIntPosition_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPhysicalBlackPortIntPosition_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareWiredPhysicalBlackPortIntPosition n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPhysicalBlackPortIntPosition_injective n

/--
[fkIsingSquareWiredPortNext_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortNext_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPortNext n hn omega d ≠ d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortNext_ne n hn omega d

/--
[fkIsingSquareWiredUnitDiagonalTangentCode_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalTangentCode_zero_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalTangentCode 0 = 5 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalTangentCode_zero

/--
[fkIsingSquareWiredUnitDiagonalTangentCode_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalTangentCode_one_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalTangentCode 1 = 3 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalTangentCode_one

/--
[fkIsingSquareWiredUnitDiagonalTangentCode_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalTangentCode_two_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalTangentCode 2 = 7 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalTangentCode_two

/--
[fkIsingSquareWiredUnitDiagonalTangentCode_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalTangentCode_three_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalTangentCode 3 = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalTangentCode_three

/--
[fkIsingSquareWiredUnitDiagonalAxis_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalAxis_zero_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalAxis 0 = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalAxis_zero

/--
[fkIsingSquareWiredUnitDiagonalAxis_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalAxis_one_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalAxis 1 = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalAxis_one

/--
[fkIsingSquareWiredUnitDiagonalAxis_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalAxis_two_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalAxis 2 = 3 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalAxis_two

/--
[fkIsingSquareWiredUnitDiagonalAxis_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalAxis_three_eq :
-- imply
  fkIsingSquareWiredUnitDiagonalAxis 3 = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalAxis_three

/--
[fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis_eq
  {a : Fin 4} :
-- imply
  fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep a) = (1 + Complex.I) * StatMech.FrontierA.kwRectilinearVector (fkIsingSquareWiredUnitDiagonalAxis a) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis a

/--
[fkIsingSquareWiredUnitDiagonal_turnPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonal_turnPhase_eq
  {a b : Fin 4}
-- given
  (hnu : fkIsingSquareWiredUnitDiagonalAxis b ≠ fkIsingSquareWiredUnitDiagonalAxis a + 2) :
-- imply
  StatMech.FrontierA.kwVectorTurnPhase (fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep a)) (fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep b)) = Complex.exp (((((fkIsingSquareSignedEighthTurn (fkIsingSquareWiredUnitDiagonalTangentCode a) (fkIsingSquareWiredUnitDiagonalTangentCode b) : Int) : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonal_turnPhase a b hnu

/--
[fkIsingSquareWiredExpandedDartStepIndex_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedDartStepIndex_spec_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : (fkIsingSquareWiredExpandedGraph n hn omega).Dart}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredExpandedIntPosition n hn d.snd = fkIsingSquareWiredExpandedIntPosition n hn d.fst + fkIsingSquareWiredUnitDiagonalStep (fkIsingSquareWiredExpandedDartStepIndex n hn omega d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega d

/--
[fkIsingSquareWiredExpandedDart_vector_eq_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedDart_vector_eq_step_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : (fkIsingSquareWiredExpandedGraph n hn omega).Dart}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredExpandedEmbedding n hn omega).vertex d.snd - (fkIsingSquareWiredExpandedEmbedding n hn omega).vertex d.fst = fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep (fkIsingSquareWiredExpandedDartStepIndex n hn omega d)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedDart_vector_eq_step n hn omega d

/--
[fkIsingSquareWiredUnitDiagonalAxis_opposite_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredUnitDiagonalAxis_opposite_step_eq
  {a b : Fin 4}
-- given
  (h : fkIsingSquareWiredUnitDiagonalAxis b = fkIsingSquareWiredUnitDiagonalAxis a + 2) :
-- imply
  fkIsingSquareWiredUnitDiagonalStep b = -fkIsingSquareWiredUnitDiagonalStep a := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredUnitDiagonalAxis_opposite_step a b h

/--
[fkIsingSquareWiredExpandedCycle_step_not_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedCycle_step_not_opposite_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {root : FKIsingSquareWiredExpandedCarrier n}
  {p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root}
-- given
  (hn : 0 < n)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ ∀ k : Fin p.darts.length, fkIsingSquareWiredUnitDiagonalAxis (fkIsingSquareWiredExpandedDartStepIndex n hn omega (StatMech.FrontierA.kwGraphCycleDartLoop p (k + 1))) ≠ fkIsingSquareWiredUnitDiagonalAxis (fkIsingSquareWiredExpandedDartStepIndex n hn omega (StatMech.FrontierA.kwGraphCycleDartLoop p k)) + 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedCycle_step_not_opposite n hn omega p hp

/--
[fkIsingSquareWiredExpandedCycle_direction_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedCycle_direction_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {root : FKIsingSquareWiredExpandedCarrier n}
  {p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root}
-- given
  (hn : 0 < n)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ let loop := StatMech.FrontierA.kwGraphCycleDartLoop p let direction := fkIsingSquareWiredExpandedDartStepIndex n hn omega (∑ k : Fin p.darts.length, fkIsingSquareSignedEighthTurn (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop k))) (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop (k + 1))))) ≡ 8 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedCycle_direction_turn_mod_sixteen n hn omega p hp

/--
[fkIsingSquareWiredPortIntPosition_localMate_exact_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortIntPosition_localMate_exact_step_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWiredPortIntPosition n (FKIsingMedialDart.localMate omega d) = fkIsingSquareWiredPortIntPosition n d + fkIsingSquareWiredUnitDiagonalStep (fkIsingSquareWiredLocalStepIndex omega d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortIntPosition_localMate_exact_step n omega d

/--
[fkIsingSquareWiredRingStepIndex_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_zero_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 0 = 3 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_zero

/--
[fkIsingSquareWiredRingStepIndex_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_one_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 1 = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_one

/--
[fkIsingSquareWiredRingStepIndex_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_two_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 2 = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_two

/--
[fkIsingSquareWiredRingStepIndex_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_three_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 3 = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_three

/--
[fkIsingSquareWiredRingStepIndex_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_four_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 4 = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_four

/--
[fkIsingSquareWiredRingStepIndex_five](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_five_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 5 = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_five

/--
[fkIsingSquareWiredRingStepIndex_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_six_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 6 = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_six

/--
[fkIsingSquareWiredRingStepIndex_seven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingStepIndex_seven_eq :
-- imply
  fkIsingSquareWiredRingStepIndex 7 = 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingStepIndex_seven

/--
[fkIsingSquareWiredForwardRingStepWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingStepWord_ne_nil_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredForwardRingStepWord n hn d ≠ [] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingStepWord_ne_nil n hn d

/--
[fkIsingSquareWiredOrdinaryBondStepWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondStepWord_ne_nil_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredOrdinaryBondStepWord n hn d ≠ [] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn d

/--
[fkIsingSquareWiredPortMacroStepWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroStepWord_ne_nil_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  fkIsingSquareWiredPortMacroStepWord n hn omega d ≠ [] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroStepWord_ne_nil n hn omega d hsource hterminal

/--
[fkIsingSquareSignedEighthTurn_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareSignedEighthTurn_congr_eq
  {a b c d : Int}
-- given
  (ha : a ≡ b [ZMOD 8])
  (hc : c ≡ d [ZMOD 8]) :
-- imply
  fkIsingSquareSignedEighthTurn a c = fkIsingSquareSignedEighthTurn b d := by
-- proof
  apply StatMech.Universality.fkIsingSquareSignedEighthTurn_congr ha hc

/--
[fkIsingSquareWiredForwardRingSlotWord_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_length_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection} :
-- imply
  (fkIsingSquareWiredForwardRingSlotWord n u d).length = (fkIsingSquareWiredBondArcLength n u d).val + 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_length n u d

/--
[fkIsingSquareWiredRingArcContains_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingArcContains_active_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
  {i : Fin 8}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d)
  (hi : fkIsingSquareWiredRingArcContains n u d i) :
-- imply
  fkIsingSquareWiredSlotRingActive n (u, i) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingArcContains_active n u d hd hi

/--
[fkIsingSquareWiredForwardRingSlotWord_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_isChain_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  List.IsChain (fkIsingSquareWiredSlotRingGraph n).Adj (fkIsingSquareWiredForwardRingSlotWord n u d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_isChain n u d hd

/--
[fkIsingSquareWiredForwardRingSlotWord_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_nodup_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection} :
-- imply
  (fkIsingSquareWiredForwardRingSlotWord n u d).Nodup := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_nodup n u d

/--
[fkIsingSquareWiredForwardRingSlotWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_ne_nil_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection} :
-- imply
  fkIsingSquareWiredForwardRingSlotWord n u d ≠ [] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_ne_nil n u d

/--
[fkIsingSquareWiredSlotIntPosition_succ_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotIntPosition_succ_step_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {i : Fin 8} :
-- imply
  fkIsingSquareWiredSlotIntPosition n (u, i + 1) = fkIsingSquareWiredSlotIntPosition n (u, i) + fkIsingSquareWiredUnitDiagonalStep (fkIsingSquareWiredRingStepIndex i) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotIntPosition_succ_step n u i

/--
[fkIsingSquareWiredSlotIntPosition_pred_reverse_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotIntPosition_pred_reverse_step_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {i : Fin 8} :
-- imply
  fkIsingSquareWiredSlotIntPosition n (u, i) = fkIsingSquareWiredSlotIntPosition n (u, i + 1) + fkIsingSquareWiredUnitDiagonalStep (fkIsingSquareWiredUnitDiagonalReverse (fkIsingSquareWiredRingStepIndex i)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotIntPosition_pred_reverse_step n u i

/--
[fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_exact_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection}
-- given
  (hn : 0 < n)
  (hd : fkIsingSquareDirectionAvailable n u d) :
-- imply
  ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk (u, fkIsingSquareWiredPortSlot d .counterclockwise) (u, fkIsingSquareWiredPortSlot (fkIsingSquareNextDirection n u d) .clockwise), p.IsPath ∧ p.support = fkIsingSquareWiredForwardRingSlotWord n u d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_exact n hn u d hd

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_length_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length = (fkIsingSquareWiredOrdinaryBondStepWord n hn d).length := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_length n hn d

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d ≠ [] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil n hn d

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).Nodup := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup n hn d

/--
[fkIsingSquareWiredForwardRingSlotWord_dropLast_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_dropLast_head_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection} :
-- imply
  (fkIsingSquareWiredForwardRingSlotWord n u d).dropLast.head (by intro hnil have hlen := congrArg List.length hnil simp at hlen have hcases := fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d rcases hcases with h | h | h <;> simp [h] at hlen) = (u, fkIsingSquareWiredPortSlot d .counterclockwise) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_dropLast_head n u d

/--
[fkIsingSquareWiredForwardRingSlotWord_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_getLast_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d : FKIsingSquareDirection} :
-- imply
  (fkIsingSquareWiredForwardRingSlotWord n u d).getLast (fkIsingSquareWiredForwardRingSlotWord_ne_nil n u d) = (u, fkIsingSquareWiredPortSlot (fkIsingSquareNextDirection n u d) .clockwise) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_getLast n u d

/--
[fkIsingSquareWiredForwardRingSlotWord_getLast_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_getLast_bondMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise) :
-- imply
  (fkIsingSquareWiredForwardRingSlotWord n (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)).getLast (fkIsingSquareWiredForwardRingSlotWord_ne_nil n (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)) = fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_getLast_bondMate n hn d hturn

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_head_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).head (fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil n hn d) = fkIsingSquareWiredDartSlot n d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_head n hn d

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_step_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hside : d.2 = .south ∨ d.2 = .north)
  (hi : i < (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length) :
-- imply
  let word := fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d let next := if h : i + 1 < word.length then word[i + 1] else fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d) fkIsingSquareWiredSlotIntPosition n next = fkIsingSquareWiredSlotIntPosition n word[i] + fkIsingSquareWiredUnitDiagonalStep (getElem (fkIsingSquareWiredOrdinaryBondStepWord n hn d) i (by rw [← fkIsingSquareWiredOrdinaryBondSlotVertexWord_length] exact hi)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_step n hn d hside i hi

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
  (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d = [fkIsingSquareWiredDartSlot n d] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton n hn d hleft hclockwise hboundary

/--
[fkIsingSquareWiredForwardRingSlotWord_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredForwardRingSlotWord_reverse_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {dir : FKIsingSquareDirection} :
-- imply
  let L := fkIsingSquareWiredBondArcLength n u dir let start := fkIsingSquareWiredPortSlot dir .counterclockwise (fkIsingSquareWiredForwardRingSlotWord n u dir).reverse = List.ofFn (fun j : Fin L.val => (u, start + ⟨L.val - j.val, by omega⟩)) ++ [(u, start)] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredForwardRingSlotWord_reverse n u dir

/--
[fkIsingSquareWiredExpandedGraph_exists_ordinary_path_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_ordinary_path_exact_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hside : d.2 = .south ∨ d.2 = .north)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))), p.IsPath ∧ p.support = (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map (fun x => (.inl x : FKIsingSquareWiredExpandedCarrier n)) ++ [.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_ordinary_path_exact n hn omega d hside hboundary

/--
[fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hside : d.2 = .south ∨ d.2 = .north)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))), p.IsPath ∧ p.support = (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map (fun x => (.inl x : FKIsingSquareWiredExpandedCarrier n)) ++ [.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))] ∧ p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) = fkIsingSquareWiredOrdinaryBondStepWord n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction n hn omega d hside hboundary

/--
[fkIsingSquareWiredBoundaryNorthIndex_boundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryNorthIndex_boundaryDart_eq
  {n : Nat}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBoundaryNorthIndex n hn (fkIsingSquareWiredBoundaryDart n hn (.north k)) = some k := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryNorthIndex_boundaryDart n hn k

/--
[fkIsingSquareWiredBoundaryNorthIndex_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryNorthIndex_eq_some_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredBoundaryNorthIndex n hn d = some k) :
-- imply
  d = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryNorthIndex_eq_some n hn d k h

/--
[fkIsingSquareWiredPortMacroVertexWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroVertexWord_ne_nil_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPortMacroVertexWord n hn omega d ≠ [] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroVertexWord_ne_nil n hn omega d

/--
[fkIsingSquareWiredPortMacroVertexWord_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroVertexWord_head_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (fkIsingSquareWiredPortMacroVertexWord n hn omega d).head (fkIsingSquareWiredPortMacroVertexWord_ne_nil n hn omega d) = .inl (fkIsingSquareWiredDartSlot n d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroVertexWord_head n hn omega d hsource hterminal

/--
[fkIsingSquareWiredExpandedGraph_exists_portNext_path_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_portNext_path_direction_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega d))), p.IsPath ∧ p.support = fkIsingSquareWiredPortMacroVertexWord n hn omega d ++ [.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega d))] ∧ p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) = fkIsingSquareWiredPortMacroStepWord n hn omega d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_portNext_path_direction n hn omega d hsource hterminal

/--
[fkIsingSquareWiredPortMacroVertexWord_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroVertexWord_nodup_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredPortMacroVertexWord n hn omega d).Nodup := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroVertexWord_nodup n hn omega d

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {x : FKIsingSquareWiredSlotCarrier n}
-- given
  (hn : 0 < n)
  (hx : x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)
  (havail : fkIsingSquareWiredSlotAvailable n x) :
-- imply
  x = fkIsingSquareWiredDartSlot n d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start n hn d hx havail

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {x : FKIsingSquareWiredSlotCarrier n}
-- given
  (hn : 0 < n)
  (hx : x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)
  (hunavailable : ¬fkIsingSquareWiredSlotAvailable n x) :
-- imply
  x.1 = fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondArcBase n hn d) ∧ fkIsingSquareWiredRingArcContains n x.1 (fkIsingSquareDartDirection n (fkIsingSquareWiredBondArcBase n hn d)) x.2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner n hn d hx hunavailable

/--
[fkIsingSquareWiredPortMacroVertexWord_available_eq_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroVertexWord_available_eq_start_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {x : FKIsingSquareWiredSlotCarrier n}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hx : (.inl x : FKIsingSquareWiredExpandedCarrier n) ∈ fkIsingSquareWiredPortMacroVertexWord n hn omega d)
  (havail : fkIsingSquareWiredSlotAvailable n x) :
-- imply
  x = fkIsingSquareWiredDartSlot n d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroVertexWord_available_eq_start n hn omega d hsource hterminal hx havail

/--
[fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (hside : d.2 = .south ∨ d.2 = .north)
  (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  (fkIsingSquareLeftVerticalUpper n hn k, 6) ∉ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle n hn d hside hboundary k

/--
[fkIsingSquareWiredSlotAvailable_dartSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredSlotAvailable_dartSlot_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWiredSlotAvailable n (fkIsingSquareWiredDartSlot n d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredSlotAvailable_dartSlot n d

/--
[fkIsingSquareWiredPortMacroVertexWord_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroVertexWord_inr_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n)
  (h : (.inr k : FKIsingSquareWiredExpandedCarrier n) ∈ fkIsingSquareWiredPortMacroVertexWord n hn omega d) :
-- imply
  d = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroVertexWord_inr n hn omega d k h

/--
[fkIsingSquareWiredPortMacroVertexWord_unavailable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroVertexWord_unavailable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {x : FKIsingSquareWiredSlotCarrier n}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hx : (.inl x : FKIsingSquareWiredExpandedCarrier n) ∈ fkIsingSquareWiredPortMacroVertexWord n hn omega d)
  (hunavailable : ¬fkIsingSquareWiredSlotAvailable n x) :
-- imply
  (d.2 = .south ∨ d.2 = .north) ∧ d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) ∧ x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d ∨ ∃ k : Fin (2 * n), d = fkIsingSquareWiredBoundaryDart n hn (.north k) ∧ x = (fkIsingSquareLeftVerticalUpper n hn k, 6) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroVertexWord_unavailable n hn omega d hsource hterminal hx hunavailable

/--
[fkIsingSquareWiredBondArcBase_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondArcBase_corner_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareSideCorner (fkIsingSquareWiredBondArcBase n hn d).2).2 = .counterclockwise := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondArcBase_corner n hn d

/--
[fkIsingSquareWiredBondArcBase_eq_of_endpoint_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondArcBase_eq_of_endpoint_direction_eq
  {n : Nat}
  {d e : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hendpoint : fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondArcBase n hn d) = fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondArcBase n hn e))
  (hdirection : fkIsingSquareDartDirection n (fkIsingSquareWiredBondArcBase n hn d) = fkIsingSquareDartDirection n (fkIsingSquareWiredBondArcBase n hn e)) :
-- imply
  fkIsingSquareWiredBondArcBase n hn d = fkIsingSquareWiredBondArcBase n hn e := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondArcBase_eq_of_endpoint_direction n hn d e hendpoint hdirection

/--
[fkIsingSquareWiredBondArcBase_injective_black](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondArcBase_injective_black_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d e : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hdside : d.2 = .south ∨ d.2 = .north)
  (heside : e.2 = .south ∨ e.2 = .north)
  (hdboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
  (heboundary : e ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
  (hbase : fkIsingSquareWiredBondArcBase n hn d = fkIsingSquareWiredBondArcBase n hn e) :
-- imply
  d = e := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondArcBase_injective_black n hn omega d e hdside heside hdboundary heboundary hbase

/--
[fkIsingSquareWiredRingArcContains_direction_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredRingArcContains_direction_injective_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {d e : FKIsingSquareDirection}
  {i : Fin 8}
-- given
  (hd : fkIsingSquareDirectionAvailable n u d)
  (he : fkIsingSquareDirectionAvailable n u e)
  (hdi : fkIsingSquareWiredRingArcContains n u d i)
  (hei : fkIsingSquareWiredRingArcContains n u e i) :
-- imply
  d = e := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRingArcContains_direction_injective n u d e hd he hdi hei

/--
[fkIsingSquareWiredPortMacroVertexWord_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroVertexWord_disjoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d e : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hdsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hesource : e ≠ fkIsingSquareWiredSourceDart n hn)
  (heterminal : e ≠ fkIsingSquareWiredTerminalDart n hn)
  (hne : d ≠ e) :
-- imply
  List.Disjoint (fkIsingSquareWiredPortMacroVertexWord n hn omega d) (fkIsingSquareWiredPortMacroVertexWord n hn omega e) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroVertexWord_disjoint n hn omega d e hdsource hdterminal hesource heterminal hne

/--
[fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_direction_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Nat}
-- given
  (hn : 0 < n)
  (hsource : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n ((fkIsingSquareWiredPortNext n hn omega)^[k] d))), let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k p.support = darts.flatMap (fkIsingSquareWiredPortMacroVertexWord n hn omega) ++ [.inl (fkIsingSquareWiredDartSlot n ((fkIsingSquareWiredPortNext n hn omega)^[k] d))] ∧ p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) = darts.flatMap (fkIsingSquareWiredPortMacroStepWord n hn omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_direction n hn omega d k hsource hterminal

/--
[fkIsingSquareWired_portNext_two_cycle_macro_length_ne_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_portNext_two_cycle_macro_length_ne_two_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hdsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hfsource : fkIsingSquareWiredPortNext n hn omega d ≠ fkIsingSquareWiredSourceDart n hn)
  (hfterminal : fkIsingSquareWiredPortNext n hn omega d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hclose : (fkIsingSquareWiredPortNext n hn omega)^[2] d = d) :
-- imply
  (fkIsingSquareWiredPortMacroStepWord n hn omega d).length + (fkIsingSquareWiredPortMacroStepWord n hn omega (fkIsingSquareWiredPortNext n hn omega d)).length ≠ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_portNext_two_cycle_macro_length_ne_two n hn omega d hdsource hdterminal hfsource hfterminal hclose

/--
[fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
-- imply
  fkIsingSquareWiredTransitionTurn n hn omega x y + fkIsingSquareWiredTransitionTurn n hn omega y x ≡ 0 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen n hn omega hxy

/--
[fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
  {p : (fkIsingSquareWiredLoopGraph n hn omega).Walk x y}
-- given
  (hn : 0 < n) :
-- imply
  carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) p.support + carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) p.reverse.support ≡ 0 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen n hn omega p

/--
[fkIsingSquareWiredPortMacroCodeWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortMacroCodeWord_ne_nil_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPortMacroCodeWord n hn omega d ≠ [] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d

/--
[fkIsingSquareWired_macro_turn_coboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_macro_turn_coboundary_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hsourceNext : fkIsingSquareWiredPortNext n hn omega d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminalNext : fkIsingSquareWiredPortNext n hn omega d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega let f := fkIsingSquareWiredPortNext n hn omega carrierAdjacentSum fkIsingSquareSignedEighthTurn (code d) + fkIsingSquareSignedEighthTurn ((code d).getLast (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d)) ((code (f d)).head (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (f d))) ≡ fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredBlackOfDart n d).1 (fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n d).1) + fkIsingSquareWiredMacroGauge n hn omega (f d) - fkIsingSquareWiredMacroGauge n hn omega d [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_macro_turn_coboundary n hn omega d hsource hterminal hsourceNext hterminalNext

/--
[fkIsingSquareWired_macroCode_cycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_macroCode_cycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {darts : List (FKIsingMedialDart (fkSquareBoxPlanar n))}
-- given
  (hn : 0 < n)
  (hdarts : darts ≠ [])
  (hsource : ∀ d ∈ darts, d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ d ∈ darts, d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hsourceNext : ∀ d ∈ darts, fkIsingSquareWiredPortNext n hn omega d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminalNext : ∀ d ∈ darts, fkIsingSquareWiredPortNext n hn omega d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hchain : darts.Chain' fun d e => e = fkIsingSquareWiredPortNext n hn omega d)
  (hclose : fkIsingSquareWiredPortNext n hn omega (darts.getLast hdarts) = darts.head hdarts) :
-- imply
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega let word := darts.flatMap code carrierAdjacentSum fkIsingSquareSignedEighthTurn word + fkIsingSquareSignedEighthTurn (word.getLast (List.flatMap_ne_nil_of_ne_nil code (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega) darts hdarts)) (word.head (List.flatMap_ne_nil_of_ne_nil code (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega) darts hdarts)) ≡ (darts.map fun d => fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredBlackOfDart n d).1 (fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n d).1)).sum [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_macroCode_cycle_turn_mod_sixteen n hn omega darts hdarts hsource hterminal hsourceNext hterminalNext hchain hclose

/--
[fkIsingSquareWired_portNext_iterate_macroCode_cycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_portNext_iterate_macroCode_cycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Nat}
-- given
  (hn : 0 < n)
  (hk : 0 < k)
  (hclose : (fkIsingSquareWiredPortNext n hn omega)^[k] d = d)
  (hsource : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k let code := fkIsingSquareWiredPortMacroCodeWord n hn omega let word := darts.flatMap code carrierAdjacentSum fkIsingSquareSignedEighthTurn word + fkIsingSquareSignedEighthTurn (word.getLast (by exact List.flatMap_ne_nil_of_ne_nil code (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega) darts (by simp [darts, hk.ne']))) (word.head (by exact List.flatMap_ne_nil_of_ne_nil code (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega) darts (by simp [darts, hk.ne']))) ≡ (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredBlackOfDart n q).1 (fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n q).1)).sum [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_portNext_iterate_macroCode_cycle_turn_mod_sixteen n hn omega d k hk hclose hsource hterminal

/--
[fkIsingSquareWiredBoundaryEmbedding_south_eq_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryEmbedding_south_eq_source_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : (e, .south) ∈ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  (e, .south) = fkIsingSquareWiredSourceDart n hn := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryEmbedding_south_eq_source n hn e h

/--
[fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : (e, .north) ∈ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
-- imply
  (e, .north) = fkIsingSquareWiredTerminalDart n hn ∨ ∃ k : Fin (2 * n), (e, .north) = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north n hn e h

/--
[fkIsingSquareWiredExpandedGraph_reachable_portNext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_reachable_portNext_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (fkIsingSquareWiredExpandedGraph n hn omega).Reachable (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_reachable_portNext n hn omega d hsource hterminal

/--
[fkIsingSquareWiredExpandedGraph_exists_portNext_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_portNext_path_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega d))), p.IsPath ∧ ¬p.Nil := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_portNext_path n hn omega d hsource hterminal

/--
[fkIsingSquareWiredExpandedGraph_exists_literal_portNext_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_literal_portNext_path_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega d))), p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_literal_portNext_path n hn omega d hsource hterminal

/--
[fkIsingSquareWiredExpandedGraph_exists_portNext_path_avoids_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_portNext_path_avoids_local_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {localDart d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hdifferent : d.2 = .west ∨ d.2 = .east → s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart))) ≠ s((.inl (fkIsingSquareWiredDartSlot n d) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega d)))) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega d))), p.IsPath ∧ s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_portNext_path_avoids_local n hn omega localDart d hsource hterminal hdifferent

/--
[fkIsingSquareWired_local_edge_eq_iff_start_or_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_local_edge_eq_iff_start_or_mate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d localDart : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (h : s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart))) = s((.inl (fkIsingSquareWiredDartSlot n d) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega d)))) :
-- imply
  d = localDart ∨ d = FKIsingMedialDart.localMate omega localDart := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_local_edge_eq_iff_start_or_mate n omega d localDart h

/--
[fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Nat}
-- given
  (hn : 0 < n)
  (hsource : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n ((fkIsingSquareWiredPortNext n hn omega)^[k] d))), k ≤ p.length := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk n hn omega d k hsource hterminal

/--
[fkIsingSquareWiredExpandedGraph_reachable_portNext_iterate_delete_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_reachable_portNext_iterate_delete_local_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {localDart d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Nat}
-- given
  (hn : 0 < n)
  (hsource : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn)
  (hdifferent : ∀ i < k, let q := (fkIsingSquareWiredPortNext n hn omega)^[i] d (q.2 = .west ∨ q.2 = .east) → s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart))) ≠ s((.inl (fkIsingSquareWiredDartSlot n q) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (fkIsingSquareWiredPortNext n hn omega q)))) :
-- imply
  ((fkIsingSquareWiredExpandedGraph n hn omega).deleteEdges {s((.inl (fkIsingSquareWiredDartSlot n localDart) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega localDart)))}).Reachable (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n ((fkIsingSquareWiredPortNext n hn omega)^[k] d))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_reachable_portNext_iterate_delete_local n hn omega localDart d k hsource hterminal hdifferent

/--
[fkIsingSquareWiredBlackBoundaryPerm_blackOfDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackBoundaryPerm_blackOfDart_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  fkIsingSquareWiredBlackBoundaryPerm n hn omega (fkIsingSquareWiredBlackOfDart n d) = fkIsingSquareWiredBlackOfDart n (fkIsingSquareWiredPortNext n hn omega d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackBoundaryPerm_blackOfDart n hn omega d hsource hterminal

/--
[fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Nat}
-- given
  (hn : 0 < n)
  (hsource : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (fkIsingSquareWiredBlackBoundaryPerm n hn omega ^ k) (fkIsingSquareWiredBlackOfDart n d) = fkIsingSquareWiredBlackOfDart n ((fkIsingSquareWiredPortNext n hn omega)^[k] d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart n hn omega d k hsource hterminal

/--
[fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable (fkIsingSquareWiredBlackOfDart n d).1 .source) :
-- imply
  ∀ i, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn ∧ (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source n hn omega d hroot

/--
[fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hmove : fkIsingSquareWiredBlackBoundaryPerm n hn omega (fkIsingSquareWiredBlackOfDart n d) ≠ fkIsingSquareWiredBlackOfDart n d)
  (hsource : ∀ i < ((fkIsingSquareWiredBlackBoundaryPerm n hn omega).cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ i < ((fkIsingSquareWiredBlackBoundaryPerm n hn omega).cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n d)), ¬p.Nil := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk n hn omega d hmove hsource hterminal

/--
[fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hdside : d.2 = .west ∨ d.2 = .east)
  (hmateWest : (FKIsingMedialDart.localMate omega d).2 ≠ .west)
  (hmateEast : (FKIsingMedialDart.localMate omega d).2 ≠ .east)
  (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable (fkIsingSquareWiredBlackOfDart n d).1 .source) :
-- imply
  ∃ root p, p.IsCycle ∧ s((.inl (fkIsingSquareWiredDartSlot n d) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (FKIsingMedialDart.localMate omega d))) ∈ (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root).edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit n hn omega d hdside hmateWest hmateEast hroot

/--
[fkIsingSquareWiredExpandedGraph_exists_direction_cycle_of_local_black_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredExpandedGraph_exists_direction_cycle_of_local_black_orbit_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable (fkIsingSquareWiredBlackOfDart n d).1 .source) :
-- imply
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl (fkIsingSquareWiredDartSlot n d)) (.inl (fkIsingSquareWiredDartSlot n d)), p.IsCycle ∧ p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) = darts.flatMap (fkIsingSquareWiredPortMacroStepWord n hn omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExpandedGraph_exists_direction_cycle_of_local_black_orbit n hn omega d hroot

/--
[fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable (fkIsingSquareWiredBlackOfDart n d).1 .source) :
-- imply
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredBlackOfDart n q).1 (fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n q).1)).sum ≡ 8 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen n hn omega d hroot

/--
[fkIsingSquareWiredTransitionTurn_completedIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionTurn_completedIncidence_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredTransitionTurn n hn omega x (fkIsingSquareWiredCompletedIncidenceEquiv n x) = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionTurn_completedIncidence n hn omega x

/--
[fkIsingSquareWiredCarrierMacroVertexWord_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredCarrierMacroVertexWord_nodup_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCarrierMacroVertexWord n hn omega d).Nodup := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCarrierMacroVertexWord_nodup n hn omega d

/--
[fkIsingSquareWiredCarrierMacroVertexWord_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredCarrierMacroVertexWord_disjoint_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d e : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hne : d ≠ e) :
-- imply
  List.Disjoint (fkIsingSquareWiredCarrierMacroVertexWord n hn omega d) (fkIsingSquareWiredCarrierMacroVertexWord n hn omega e) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCarrierMacroVertexWord_disjoint n hn omega d e hne

/--
[fkIsingSquareWiredCompletedGraph_exists_portNext_carrier_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedGraph_exists_portNext_carrier_path_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk (fkIsingSquareWiredBlackOfDart n d).1 (fkIsingSquareWiredBlackOfDart n (fkIsingSquareWiredPortNext n hn omega d)).1, p.IsPath ∧ p.support = fkIsingSquareWiredCarrierMacroVertexWord n hn omega d ++ [(fkIsingSquareWiredBlackOfDart n (fkIsingSquareWiredPortNext n hn omega d)).1] ∧ carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) p.support = fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredBlackOfDart n d).1 (fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n d).1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedGraph_exists_portNext_carrier_path n hn omega d hsource hterminal

/--
[fkIsingSquareWiredCompletedGraph_exists_portNext_iterate_carrier_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedGraph_exists_portNext_iterate_carrier_walk_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
  {k : Nat}
-- given
  (hn : 0 < n)
  (hsource : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : ∀ i < k, (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk (fkIsingSquareWiredBlackOfDart n d).1 (fkIsingSquareWiredBlackOfDart n ((fkIsingSquareWiredPortNext n hn omega)^[k] d)).1, let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k p.support = darts.flatMap (fkIsingSquareWiredCarrierMacroVertexWord n hn omega) ++ [(fkIsingSquareWiredBlackOfDart n ((fkIsingSquareWiredPortNext n hn omega)^[k] d)).1] ∧ carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) p.support = (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredBlackOfDart n q).1 (fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedGraph_exists_portNext_iterate_carrier_walk n hn omega d k hsource hterminal

/--
[fkIsingSquareWiredCompletedLoopGraph_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_isCycles_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).IsCycles := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_isCycles n hn omega

/--
[fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable (fkIsingSquareWiredBlackOfDart n d).1 .source) :
-- imply
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk (fkIsingSquareWiredBlackOfDart n d).1 (fkIsingSquareWiredBlackOfDart n d).1, p.IsCycle ∧ p.snd = fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n d).1 ∧ carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) p.support = (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega (fkIsingSquareWiredBlackOfDart n q).1 (fkIsingSquareWiredTransitionMate n hn omega (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit n hn omega d hroot

/--
[fkIsingSquareWired_one_visit_west_cycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_cycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)), s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk (.dart (e, .east)) (.dart (e, .north))}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hr : r.IsPath) :
-- imply
  carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .north)) (.dart (e, .east)) ≡ 8 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_cycle_turn_mod_sixteen n hn omega e hwest heast r hr

/--
[fkIsingSquareWired_one_visit_east_cycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_cycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)), s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk (.dart (e, .west)) (.dart (e, .south))}
-- given
  (hn : 0 < n)
  (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hr : r.IsPath) :
-- imply
  carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .south)) (.dart (e, .west)) ≡ 8 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_cycle_turn_mod_sixteen n hn omega e hwest heast r hr

/--
[fkIsingSquareWired_one_visit_west_inserted_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_inserted_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_inserted_phase n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_east_inserted_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_inserted_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_inserted_phase n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_west_exists_closed_macro_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_exists_closed_macro_walk_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn (setClosed e.1 omega)).Walk (.inl (fkIsingSquareWiredDartSlot n (e, .east))) (.inl (fkIsingSquareWiredDartSlot n (e, .east))), ¬p.Nil := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_exists_closed_macro_walk n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_east_exists_closed_macro_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_exists_closed_macro_walk_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  ∃ p : (fkIsingSquareWiredExpandedGraph n hn (setClosed e.1 omega)).Walk (.inl (fkIsingSquareWiredDartSlot n (e, .west))) (.inl (fkIsingSquareWiredDartSlot n (e, .west))), ¬p.Nil := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_exists_closed_macro_walk n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_west_exists_expanded_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_exists_expanded_cycle_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  ∃ root p, p.IsCycle ∧ s((.inl (fkIsingSquareWiredDartSlot n (e, .east)) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (e, .north))) ∈ (p : (fkIsingSquareWiredExpandedGraph n hn (setClosed e.1 omega)).Walk root root).edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_exists_expanded_cycle n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_east_exists_expanded_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_exists_expanded_cycle_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  ∃ root p, p.IsCycle ∧ s((.inl (fkIsingSquareWiredDartSlot n (e, .west)) : FKIsingSquareWiredExpandedCarrier n), .inl (fkIsingSquareWiredDartSlot n (e, .south))) ∈ (p : (fkIsingSquareWiredExpandedGraph n hn (setClosed e.1 omega)).Walk root root).edges := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_exists_expanded_cycle n hn omega e hwest heast


-- created on 2026-10-23
