import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
open Finset Set SimpleGraph Function MeasureTheory StatMech StatMech.Lattice


/--
[dartPrimalEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma dartPrimalEdge_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart} :
-- imply
  dartPrimalEdge e = s(e.tail, e.head) := by
-- proof
  apply StatMech.Lattice.dartPrimalEdge_eq e

/--
[boundaryDart_primalEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma boundaryDart_primalEdge_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart (cluster 2 ω o) e) :
-- imply
  ω (dartPrimalEdge e) = false := by
-- proof
  apply StatMech.Lattice.boundaryDart_primalEdge_isClosed o he

/--
[canonicalContour_length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalContour_length_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (canonicalContour (ω := ω) hfin).length = dartOrbitPeriod (cluster 2 ω (origin 2)) ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
-- proof
  apply StatMech.Lattice.canonicalContour_length_eq hfin

/--
[canonicalContour_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalContour_length_pos_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  0 < (canonicalContour (ω := ω) hfin).length := by
-- proof
  apply StatMech.Lattice.canonicalContour_length_pos hfin

/--
[exitDart_tail_on_posAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma exitDart_tail_on_posAxis_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (exitDart (ω := ω) hfin).tail = ![(exitIndex (ω := ω) hfin : ℤ), 0] := by
-- proof
  apply StatMech.Lattice.exitDart_tail_on_posAxis hfin

/--
[orbitDart_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma orbitDart_isBoundaryDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  IsBoundaryDart (cluster 2 ω (origin 2)) ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin)) := by
-- proof
  apply StatMech.Lattice.orbitDart_isBoundaryDart hfin n

/--
[orbitDart_primalEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma orbitDart_primalEdge_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ω (dartPrimalEdge ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin))) = false := by
-- proof
  apply StatMech.Lattice.orbitDart_primalEdge_isClosed hfin n

/--
[mem_canonicalContourDarts_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma mem_canonicalContourDarts_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {D : Dart}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  D ∈ canonicalContourDarts (ω := ω) hfin ↔ ∃ k < dartOrbitPeriod (cluster 2 ω (origin 2)) ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩, (dartNext (cluster 2 ω (origin 2)))^[k + 1] (exitDart (ω := ω) hfin) = D := by
-- proof
  apply StatMech.Lattice.mem_canonicalContourDarts_iff hfin D

/--
[mem_closedDartContourEvent_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma mem_closedDartContourEvent_canonical_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ω ∈ closedDartContourEvent (ω := ω) hfin := by
-- proof
  apply StatMech.Lattice.mem_closedDartContourEvent_canonical hfin

/--
[closedDartContourEvent_eq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma closedDartContourEvent_eq_pi_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  closedDartContourEvent (ω := ω) hfin = ((canonicalPrimalEdgeFinset (ω := ω) hfin : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))).pi (fun _ => ({false} : Set Bool)) := by
-- proof
  apply StatMech.Lattice.closedDartContourEvent_eq_pi hfin

/--
[measure_closedDartContourEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma measure_closedDartContourEvent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedDartContourEvent (ω := ω) hfin) = ((1 - p : NNReal) : ENNReal) ^ (canonicalPrimalEdgeFinset (ω := ω) hfin).card := by
-- proof
  apply StatMech.Lattice.measure_closedDartContourEvent p hp hfin

/--
[dartPrimalEdge_injOn_boundaryDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma dartPrimalEdge_injOn_boundaryDarts_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (h : dartPrimalEdge e = dartPrimalEdge f) :
-- imply
  e = f := by
-- proof
  apply StatMech.Lattice.dartPrimalEdge_injOn_boundaryDarts K he hf h

/--
[canonicalContourDarts_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalContourDarts_nodup_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (canonicalContourDarts (ω := ω) hfin).Nodup := by
-- proof
  apply StatMech.Lattice.canonicalContourDarts_nodup hfin

/--
[canonicalPrimalEdge_list_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalPrimalEdge_list_nodup_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ((canonicalContourDarts (ω := ω) hfin).map dartPrimalEdge).Nodup := by
-- proof
  apply StatMech.Lattice.canonicalPrimalEdge_list_nodup hfin

/--
[canonicalPrimalEdgeFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalPrimalEdgeFinset_card_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (canonicalPrimalEdgeFinset (ω := ω) hfin).card = dartOrbitPeriod (cluster 2 ω (origin 2)) ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
-- proof
  apply StatMech.Lattice.canonicalPrimalEdgeFinset_card hfin

/--
[measure_closedDartContourEvent_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma measure_closedDartContourEvent_period_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedDartContourEvent (ω := ω) hfin) = ((1 - p : NNReal) : ENNReal) ^ (dartOrbitPeriod (cluster 2 ω (origin 2)) ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩) := by
-- proof
  apply StatMech.Lattice.measure_closedDartContourEvent_period p hp hfin

/--
[canonicalFaceWalkAux_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalFaceWalkAux_length_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (canonicalFaceWalkAux K e he n).length = n := by
-- proof
  apply StatMech.Lattice.canonicalFaceWalkAux_length K e he n

/--
[canonicalFaceWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalFaceWalk_length_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (canonicalFaceWalk (ω := ω) hfin).length = dartOrbitPeriod (cluster 2 ω (origin 2)) ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
-- proof
  apply StatMech.Lattice.canonicalFaceWalk_length hfin

/--
[canonicalFaceWalk_basepoint_mem_anchorFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma canonicalFaceWalk_basepoint_mem_anchorFinset_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hwind : CanonicalContourWinds ω hfin) :
-- imply
  exitFaceUp (ω := ω) hfin ∈ StatMech.Percolation.anchorFinset (canonicalFaceWalk (ω := ω) hfin).length := by
-- proof
  apply StatMech.Lattice.canonicalFaceWalk_basepoint_mem_anchorFinset hfin hwind

/--
[pc_lt_one_via_canonicalContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean)
-/
@[path]
private lemma pc_lt_one_via_canonicalContour_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), AnchoredCycleExists ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.pc_lt_one_via_canonicalContour hres


-- created on 2026-10-23
