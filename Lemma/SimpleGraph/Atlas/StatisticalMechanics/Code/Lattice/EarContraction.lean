import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
open SimpleGraph Function StatMech StatMech.Lattice


/--
[cornerBalance_eq_totalTurnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cornerBalance_eq_totalTurnZ_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  cornerBalance K a = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.cornerBalance_eq_totalTurnZ K a

/--
[simplePolygonCornerBalance_iff_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma simplePolygonCornerBalance_iff_cornerBalance_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  SimplePolygonCornerBalance K a ↔ (cornerBalance K a = 4 ∨ cornerBalance K a = -4) := by
-- proof
  apply StatMech.Lattice.simplePolygonCornerBalance_iff_cornerBalance K a

/--
[extremeCell_up_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma extremeCell_up_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  c + ![0, 1] ∉ K := by
-- proof
  apply StatMech.Lattice.extremeCell_up_nmem K c hc

/--
[extremeCell_left_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma extremeCell_left_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  c + ![-1, 0] ∉ K := by
-- proof
  apply StatMech.Lattice.extremeCell_left_nmem K c hc

/--
[adj_neighbor_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma adj_neighbor_cases_eq
  {v c : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj v c) :
-- imply
  v = c + ![1, 0] ∨ v = c + ![-1, 0] ∨ v = c + ![0, 1] ∨ v = c + ![0, -1] := by
-- proof
  apply StatMech.Lattice.adj_neighbor_cases v c hadj

/--
[extremeCell_neighbor_right_or_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma extremeCell_neighbor_right_or_down_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (hv : v ∈ K)
  (hadj : (hypercubicLattice 2).Adj v c) :
-- imply
  v = c + ![1, 0] ∨ v = c + ![0, -1] := by
-- proof
  apply StatMech.Lattice.extremeCell_neighbor_right_or_down K c v hc hv hadj

/--
[cellConnected_diff_of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cellConnected_diff_of_iso_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : c ∈ K)
  (h : (((hypercubicLattice 2).induce K).induce {(⟨c, hc⟩ : K)}ᶜ).Connected) :
-- imply
  CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Lattice.cellConnected_diff_of_iso K c hc h

/--
[cellConnected_diff_of_degree_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cellConnected_diff_of_degree_one_eq
  {K : Set (Site 2)}
  {c : Site 2}
  [Fintype ↑(((hypercubicLattice 2).induce K).neighborSet (⟨c, hc⟩ : K))]
-- given
  (hc : c ∈ K)
  (hconn : CellConnected K)
  (hdeg : ((hypercubicLattice 2).induce K).degree (⟨c, hc⟩ : K) = 1) :
-- imply
  CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Lattice.cellConnected_diff_of_degree_one K c hc hconn hdeg

/--
[mem_cutWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma mem_cutWitness_eq
  {v : Site 2} :
-- imply
  v ∈ cutWitness ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![1, 1] ∨ v = ![2, 1] := by
-- proof
  apply StatMech.Lattice.mem_cutWitness v

/--
[cw_v00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cw_v00_eq :
-- imply
  (![0, 0] : Site 2) ∈ cutWitness := by
-- proof
  apply StatMech.Lattice.cw_v00

/--
[cw_v10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cw_v10_eq :
-- imply
  (![1, 0] : Site 2) ∈ cutWitness := by
-- proof
  apply StatMech.Lattice.cw_v10

/--
[cw_v11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cw_v11_eq :
-- imply
  (![1, 1] : Site 2) ∈ cutWitness := by
-- proof
  apply StatMech.Lattice.cw_v11

/--
[cw_v21](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cw_v21_eq :
-- imply
  (![2, 1] : Site 2) ∈ cutWitness := by
-- proof
  apply StatMech.Lattice.cw_v21

/--
[cutWitness_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cutWitness_cellConnected_eq :
-- imply
  CellConnected cutWitness := by
-- proof
  apply StatMech.Lattice.cutWitness_cellConnected

/--
[cutWitness_extreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cutWitness_extreme_eq :
-- imply
  IsExtremeCell cutWitness ![1, 1] := by
-- proof
  apply StatMech.Lattice.cutWitness_extreme

/--
[mem_cutWitness_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma mem_cutWitness_diff_eq
  {v : Site 2} :
-- imply
  v ∈ cutWitness \ {![1, 1]} ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![2, 1] := by
-- proof
  apply StatMech.Lattice.mem_cutWitness_diff v

/--
[cwd_v21](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cwd_v21_eq :
-- imply
  (![2, 1] : Site 2) ∈ cutWitness \ {![1, 1]} := by
-- proof
  apply StatMech.Lattice.cwd_v21

/--
[cwd_v00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cwd_v00_eq :
-- imply
  (![0, 0] : Site 2) ∈ cutWitness \ {![1, 1]} := by
-- proof
  apply StatMech.Lattice.cwd_v00

/--
[cwd_v21_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cwd_v21_isolated_eq :
-- imply
  ((hypercubicLattice 2).induce (cutWitness \ {![1, 1]})).neighborSet ⟨![2, 1], cwd_v21⟩ = ∅ := by
-- proof
  apply StatMech.Lattice.cwd_v21_isolated

/--
[cwd_v21_ne_v00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cwd_v21_ne_v00_eq :
-- imply
  (⟨![2, 1], cwd_v21⟩ : ↑(cutWitness \ {![1, 1]})) ≠ ⟨![0, 0], cwd_v00⟩ := by
-- proof
  apply StatMech.Lattice.cwd_v21_ne_v00

/--
[cutWitness_diff_not_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cutWitness_diff_not_cellConnected_eq :
-- imply
  ¬ CellConnected (cutWitness \ {![1, 1]}) := by
-- proof
  apply StatMech.Lattice.cutWitness_diff_not_cellConnected

/--
[mem_transSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma mem_transSet_eq
  {w : Site 2}
  {K : Set (Site 2)}
  {x : Site 2} :
-- imply
  x ∈ transSet w K ↔ x - w ∈ K := by
-- proof
  apply StatMech.Lattice.mem_transSet w K x

/--
[transDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma transDart_tail_eq
  {w : Site 2}
  {e : Dart} :
-- imply
  (transDart w e).tail = e.tail + w := by
-- proof
  apply StatMech.Lattice.transDart_tail w e

/--
[transDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma transDart_dir_eq
  {w : Site 2}
  {e : Dart} :
-- imply
  (transDart w e).dir = e.dir := by
-- proof
  apply StatMech.Lattice.transDart_dir w e

/--
[transDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma transDart_head_eq
  {w : Site 2}
  {e : Dart} :
-- imply
  (transDart w e).head = e.head + w := by
-- proof
  apply StatMech.Lattice.transDart_head w e

/--
[transDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma transDart_injective_eq
  {w : Site 2} :
-- imply
  Function.Injective (transDart w) := by
-- proof
  apply StatMech.Lattice.transDart_injective w

/--
[transDart_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma transDart_boundary_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  IsBoundaryDart (transSet w K) (transDart w e) := by
-- proof
  apply StatMech.Lattice.transDart_boundary K w e he

/--
[turnZ_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma turnZ_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {e : Dart} :
-- imply
  turnZ (transSet w K) (transDart w e) = turnZ K e := by
-- proof
  apply StatMech.Lattice.turnZ_trans K w e

/--
[dartNext_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma dartNext_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {e : Dart} :
-- imply
  dartNext (transSet w K) (transDart w e) = transDart w (dartNext K e) := by
-- proof
  apply StatMech.Lattice.dartNext_trans K w e

/--
[iterate_dartNext_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma iterate_dartNext_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {e : Dart}
  {k : ℕ} :
-- imply
  (dartNext (transSet w K))^[k] (transDart w e) = transDart w ((dartNext K)^[k] e) := by
-- proof
  apply StatMech.Lattice.iterate_dartNext_trans K w e k

/--
[rightCornerCount_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma rightCornerCount_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {e : Dart}
  {p : ℕ} :
-- imply
  rightCornerCount (transSet w K) (transDart w e) p = rightCornerCount K e p := by
-- proof
  apply StatMech.Lattice.rightCornerCount_trans K w e p

/--
[leftCornerCount_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma leftCornerCount_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {e : Dart}
  {p : ℕ} :
-- imply
  leftCornerCount (transSet w K) (transDart w e) p = leftCornerCount K e p := by
-- proof
  apply StatMech.Lattice.leftCornerCount_trans K w e p

/--
[transSub_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma transSub_val_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (transSub K w a).1 = transDart w a.1 := by
-- proof
  apply StatMech.Lattice.transSub_val K w a

/--
[isPeriodicPt_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma isPeriodicPt_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ} :
-- imply
  Function.IsPeriodicPt (dartNextSub (transSet w K)) n (transSub K w a) ↔ Function.IsPeriodicPt (dartNextSub K) n a := by
-- proof
  apply StatMech.Lattice.isPeriodicPt_trans K w a n

/--
[dartOrbitPeriod_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma dartOrbitPeriod_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  dartOrbitPeriod (transSet w K) (transSub K w a) = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.dartOrbitPeriod_trans K w a

/--
[cornerBalance_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cornerBalance_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  cornerBalance (transSet w K) (transSub K w a) = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.cornerBalance_trans K w a

/--
[it1_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it1_1_eq :
-- imply
  (dartNext unitCell)^[1] ucDart1 = ucDart2 := by
-- proof
  apply StatMech.Lattice.it1_1

/--
[it1_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it1_2_eq :
-- imply
  (dartNext unitCell)^[2] ucDart1 = ucDart3 := by
-- proof
  apply StatMech.Lattice.it1_2

/--
[it1_3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it1_3_eq :
-- imply
  (dartNext unitCell)^[3] ucDart1 = ucDart0 := by
-- proof
  apply StatMech.Lattice.it1_3

/--
[it1_4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it1_4_eq :
-- imply
  (dartNext unitCell)^[4] ucDart1 = ucDart1 := by
-- proof
  apply StatMech.Lattice.it1_4

/--
[it2_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it2_1_eq :
-- imply
  (dartNext unitCell)^[1] ucDart2 = ucDart3 := by
-- proof
  apply StatMech.Lattice.it2_1

/--
[it2_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it2_2_eq :
-- imply
  (dartNext unitCell)^[2] ucDart2 = ucDart0 := by
-- proof
  apply StatMech.Lattice.it2_2

/--
[it2_3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it2_3_eq :
-- imply
  (dartNext unitCell)^[3] ucDart2 = ucDart1 := by
-- proof
  apply StatMech.Lattice.it2_3

/--
[it2_4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it2_4_eq :
-- imply
  (dartNext unitCell)^[4] ucDart2 = ucDart2 := by
-- proof
  apply StatMech.Lattice.it2_4

/--
[it3_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it3_1_eq :
-- imply
  (dartNext unitCell)^[1] ucDart3 = ucDart0 := by
-- proof
  apply StatMech.Lattice.it3_1

/--
[it3_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it3_2_eq :
-- imply
  (dartNext unitCell)^[2] ucDart3 = ucDart1 := by
-- proof
  apply StatMech.Lattice.it3_2

/--
[it3_3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it3_3_eq :
-- imply
  (dartNext unitCell)^[3] ucDart3 = ucDart2 := by
-- proof
  apply StatMech.Lattice.it3_3

/--
[it3_4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma it3_4_eq :
-- imply
  (dartNext unitCell)^[4] ucDart3 = ucDart3 := by
-- proof
  apply StatMech.Lattice.it3_4

/--
[ucBase1_period4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase1_period4_eq :
-- imply
  Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase1 := by
-- proof
  apply StatMech.Lattice.ucBase1_period4

/--
[ucBase1_notfix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase1_notfix_eq :
-- imply
  ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase1 := by
-- proof
  apply StatMech.Lattice.ucBase1_notfix

/--
[ucBase1_notper2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase1_notper2_eq :
-- imply
  ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase1 := by
-- proof
  apply StatMech.Lattice.ucBase1_notper2

/--
[ucBase1_orbitPeriod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase1_orbitPeriod_eq :
-- imply
  dartOrbitPeriod unitCell ucBase1 = 4 := by
-- proof
  apply StatMech.Lattice.ucBase1_orbitPeriod

/--
[ucBase2_period4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase2_period4_eq :
-- imply
  Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase2 := by
-- proof
  apply StatMech.Lattice.ucBase2_period4

/--
[ucBase2_notfix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase2_notfix_eq :
-- imply
  ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase2 := by
-- proof
  apply StatMech.Lattice.ucBase2_notfix

/--
[ucBase2_notper2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase2_notper2_eq :
-- imply
  ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase2 := by
-- proof
  apply StatMech.Lattice.ucBase2_notper2

/--
[ucBase2_orbitPeriod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase2_orbitPeriod_eq :
-- imply
  dartOrbitPeriod unitCell ucBase2 = 4 := by
-- proof
  apply StatMech.Lattice.ucBase2_orbitPeriod

/--
[ucBase3_period4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase3_period4_eq :
-- imply
  Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase3 := by
-- proof
  apply StatMech.Lattice.ucBase3_period4

/--
[ucBase3_notfix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase3_notfix_eq :
-- imply
  ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase3 := by
-- proof
  apply StatMech.Lattice.ucBase3_notfix

/--
[ucBase3_notper2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase3_notper2_eq :
-- imply
  ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase3 := by
-- proof
  apply StatMech.Lattice.ucBase3_notper2

/--
[ucBase3_orbitPeriod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase3_orbitPeriod_eq :
-- imply
  dartOrbitPeriod unitCell ucBase3 = 4 := by
-- proof
  apply StatMech.Lattice.ucBase3_orbitPeriod

/--
[ucBase1_totalTurnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase1_totalTurnZ_eq :
-- imply
  totalTurnZ unitCell ucDart1 4 = -4 := by
-- proof
  apply StatMech.Lattice.ucBase1_totalTurnZ

/--
[ucBase2_totalTurnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase2_totalTurnZ_eq :
-- imply
  totalTurnZ unitCell ucDart2 4 = -4 := by
-- proof
  apply StatMech.Lattice.ucBase2_totalTurnZ

/--
[ucBase3_totalTurnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma ucBase3_totalTurnZ_eq :
-- imply
  totalTurnZ unitCell ucDart3 4 = -4 := by
-- proof
  apply StatMech.Lattice.ucBase3_totalTurnZ

/--
[unitCell_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma unitCell_cornerBalance_eq
  {a : {e : Dart // IsBoundaryDart unitCell e}}
-- given
  (ha : a.1 = ucDart0 ∨ a.1 = ucDart1 ∨ a.1 = ucDart2 ∨ a.1 = ucDart3) :
-- imply
  cornerBalance unitCell a = -4 := by
-- proof
  apply StatMech.Lattice.unitCell_cornerBalance a ha

/--
[transSet_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma transSet_unitCell_eq
  {v : Site 2} :
-- imply
  transSet v unitCell = {v} := by
-- proof
  apply StatMech.Lattice.transSet_unitCell v

/--
[singleton_boundaryDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma singleton_boundaryDart_tail_eq
  {v : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart ({v} : Set (Site 2)) e) :
-- imply
  e.tail = v := by
-- proof
  apply StatMech.Lattice.singleton_boundaryDart_tail v e he

/--
[singleton_boundaryDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma singleton_boundaryDart_dir_eq
  {v : Site 2}
  {e : Dart}
-- given
  (_he : IsBoundaryDart ({v} : Set (Site 2)) e) :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
-- proof
  apply StatMech.Lattice.singleton_boundaryDart_dir v e _he

/--
[singleton_boundaryDart_eq_transDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma singleton_boundaryDart_eq_transDart_eq
  {v : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart ({v} : Set (Site 2)) e) :
-- imply
  (e = transDart v ucDart0 ∧ e.dir = ![1, 0]) ∨ (e = transDart v ucDart2 ∧ e.dir = ![-1, 0]) ∨ (e = transDart v ucDart3 ∧ e.dir = ![0, 1]) ∨ (e = transDart v ucDart1 ∧ e.dir = ![0, -1]) := by
-- proof
  apply StatMech.Lattice.singleton_boundaryDart_eq_transDart v e he

/--
[cornerBalance_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma cornerBalance_congr_eq
  {K K' : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart K' e}}
-- given
  (hKK : K = K')
  (ha : a.1 = a'.1) :
-- imply
  cornerBalance K a = cornerBalance K' a' := by
-- proof
  apply StatMech.Lattice.cornerBalance_congr K K' hKK a a' ha

/--
[singleton_cornerBalance_reduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma singleton_cornerBalance_reduce_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}}
  {b : {e : Dart // IsBoundaryDart unitCell e}}
-- given
  (he : a.1 = transDart v b.1) :
-- imply
  cornerBalance ({v} : Set (Site 2)) a = cornerBalance unitCell b := by
-- proof
  apply StatMech.Lattice.singleton_cornerBalance_reduce v a b he

/--
[singleton_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma singleton_cornerBalance_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  cornerBalance ({v} : Set (Site 2)) a = -4 := by
-- proof
  apply StatMech.Lattice.singleton_cornerBalance v a

/--
[balanceIsFour_iff_simplePolygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma balanceIsFour_iff_simplePolygon_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  BalanceIsFour K a ↔ SimplePolygonCornerBalance K a := by
-- proof
  apply StatMech.Lattice.balanceIsFour_iff_simplePolygon K a

/--
[singleton_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma singleton_balanceIsFour_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  BalanceIsFour ({v} : Set (Site 2)) a := by
-- proof
  apply StatMech.Lattice.singleton_balanceIsFour v a

/--
[balanceIsFour_of_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma balanceIsFour_of_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcontr : BalancePreservingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  BalanceIsFour K a := by
-- proof
  apply StatMech.Lattice.balanceIsFour_of_contraction hcontr K hK hne a

/--
[simplePolygonCornerBalance_of_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma simplePolygonCornerBalance_of_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcontr : BalancePreservingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  SimplePolygonCornerBalance K a := by
-- proof
  apply StatMech.Lattice.simplePolygonCornerBalance_of_contraction hcontr K hK hne a

/--
[turningIsFullRevolution_of_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_contraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcontr : BalancePreservingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_contraction hcontr K hK hne a

/--
[unitCell_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean)
-/
@[path]
private lemma unitCell_balanceIsFour_eq :
-- imply
  BalanceIsFour unitCell ucBase := by
-- proof
  apply StatMech.Lattice.unitCell_balanceIsFour


-- created on 2026-10-23
