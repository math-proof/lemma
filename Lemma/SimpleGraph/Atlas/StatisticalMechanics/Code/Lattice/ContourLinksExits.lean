import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[exitDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma exitDart_tail_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (exitDart (ω := ω) hfin).tail = axisSite (exitIndex (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.exitDart_tail hfin

/--
[exitDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma exitDart_head_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (exitDart (ω := ω) hfin).head = axisSite (exitIndex (ω := ω) hfin + 1) := by
-- proof
  apply StatMech.Lattice.exitDart_head hfin

/--
[exitDart_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma exitDart_isBoundaryDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  IsBoundaryDart (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.exitDart_isBoundaryDart hfin

/--
[exitDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma exitDart_dir_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (exitDart (ω := ω) hfin).dir = ![1, 0] := by
-- proof
  apply StatMech.Lattice.exitDart_dir hfin

/--
[leftExitDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma leftExitDart_tail_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (leftExitDart (ω := ω) hfin).tail = leftAxisSite (leftExitIndex (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.leftExitDart_tail hfin

/--
[leftExitDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma leftExitDart_head_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (leftExitDart (ω := ω) hfin).head = leftAxisSite (leftExitIndex (ω := ω) hfin + 1) := by
-- proof
  apply StatMech.Lattice.leftExitDart_head hfin

/--
[leftExitDart_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma leftExitDart_isBoundaryDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  IsBoundaryDart (cluster 2 ω (origin 2)) (leftExitDart (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.leftExitDart_isBoundaryDart hfin

/--
[leftExitDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma leftExitDart_dir_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (leftExitDart (ω := ω) hfin).dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.leftExitDart_dir hfin

/--
[dartDir_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartDir_cases_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart} :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
-- proof
  apply StatMech.Lattice.dartDir_cases e

/--
[dartFace_of_dir_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_of_dir_right_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart}
-- given
  (hd : e.dir = ![1, 0]) :
-- imply
  dartFace e = ![e.tail 0, e.tail 1] := by
-- proof
  apply StatMech.Lattice.dartFace_of_dir_right e hd

/--
[dartFace_of_dir_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_of_dir_left_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] := by
-- proof
  apply StatMech.Lattice.dartFace_of_dir_left e hd

/--
[dartFace_of_dir_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_of_dir_up_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  dartFace e = ![e.tail 0 - 1, e.tail 1] := by
-- proof
  apply StatMech.Lattice.dartFace_of_dir_up e hd

/--
[dartFace_of_dir_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_of_dir_down_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart}
-- given
  (hd : e.dir = ![0, -1]) :
-- imply
  dartFace e = ![e.tail 0, e.tail 1 - 1] := by
-- proof
  apply StatMech.Lattice.dartFace_of_dir_down e hd

/--
[dartFace_exitDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_exitDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  dartFace (exitDart (ω := ω) hfin) = exitFaceUp (ω := ω) hfin := by
-- proof
  apply StatMech.Lattice.dartFace_exitDart hfin

/--
[dartFace_leftExitDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_leftExitDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  dartFace (leftExitDart (ω := ω) hfin) = leftExitFaceDown (ω := ω) hfin := by
-- proof
  apply StatMech.Lattice.dartFace_leftExitDart hfin

/--
[dartFace_leftExitDart_coord0_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_leftExitDart_coord0_nonpos_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  dartFace (leftExitDart (ω := ω) hfin) 0 ≤ 0 := by
-- proof
  apply StatMech.Lattice.dartFace_leftExitDart_coord0_nonpos hfin

/--
[faceBoundaryGraph_adj_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma faceBoundaryGraph_adj_vert_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a b : ℤ}
-- given
  (h : ((![a, b] : Site 2) ∈ K) ↔ ((![a + 1, b] : Site 2) ∉ K)) :
-- imply
  (faceBoundaryGraph K).Adj ![a, b] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_adj_vert K a b h

/--
[faceBoundaryGraph_adj_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma faceBoundaryGraph_adj_horiz_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a b : ℤ}
-- given
  (h : ((![a, b] : Site 2) ∈ K) ↔ ((![a, b + 1] : Site 2) ∉ K)) :
-- imply
  (faceBoundaryGraph K).Adj ![a, b] ![a - 1, b] := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_adj_horiz K a b h

/--
[dart_head_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dart_head_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart} :
-- imply
  e.head = e.tail + e.dir := by
-- proof
  apply StatMech.Lattice.dart_head_eq e

/--
[dartFace_next_of_dir_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_next_of_dir_right_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hd : e.dir = ![1, 0]) :
-- imply
  dartFace (dartNext K e) = ![e.tail 0, e.tail 1 - 1] := by
-- proof
  apply StatMech.Lattice.dartFace_next_of_dir_right K e hd

/--
[dartFace_next_of_dir_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_next_of_dir_left_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  dartFace (dartNext K e) = ![e.tail 0 - 1, e.tail 1] := by
-- proof
  apply StatMech.Lattice.dartFace_next_of_dir_left K e hd

/--
[dartFace_next_of_dir_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_next_of_dir_up_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  dartFace (dartNext K e) = ![e.tail 0, e.tail 1] := by
-- proof
  apply StatMech.Lattice.dartFace_next_of_dir_up K e hd

/--
[dartFace_next_of_dir_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_next_of_dir_down_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hd : e.dir = ![0, -1]) :
-- imply
  dartFace (dartNext K e) = ![e.tail 0 - 1, e.tail 1 - 1] := by
-- proof
  apply StatMech.Lattice.dartFace_next_of_dir_down K e hd

/--
[dartFace_step_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_step_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (faceBoundaryGraph K).Adj (dartFace e) (dartFace (dartNext K e)) := by
-- proof
  apply StatMech.Lattice.dartFace_step_adj K e he

/--
[iterate_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma iterate_isBoundaryDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  IsBoundaryDart K ((dartNext K)^[n] e) := by
-- proof
  apply StatMech.Lattice.iterate_isBoundaryDart K e he n

/--
[dartFace_iterate_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_iterate_reachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (faceBoundaryGraph K).Reachable (dartFace e) (dartFace ((dartNext K)^[n] e)) := by
-- proof
  apply StatMech.Lattice.dartFace_iterate_reachable K e he n

/--
[dartFace_reachable_of_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma dartFace_reachable_of_orbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e f : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e)
  (hf : (dartNext K)^[n] e = f) :
-- imply
  (faceBoundaryGraph K).Reachable (dartFace e) (dartFace f) := by
-- proof
  apply StatMech.Lattice.dartFace_reachable_of_orbit K e f he hf

/--
[exitFaces_reachable_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma exitFaces_reachable_of_sameOrbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : ExitDartsSameOrbit ω hfin) :
-- imply
  (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.exitFaces_reachable_of_sameOrbit hfin h

/--
[pc_lt_one_via_dartOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean)
-/
@[path]
private lemma pc_lt_one_via_dartOrbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.pc_lt_one_via_dartOrbit h


-- created on 2026-10-23
