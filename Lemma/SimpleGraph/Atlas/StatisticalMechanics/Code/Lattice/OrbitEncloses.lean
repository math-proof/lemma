import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[dartOrbitFaceWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma dartOrbitFaceWalk_length_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (dartOrbitFaceWalk K e he n).length = n := by
-- proof
  apply StatMech.Lattice.dartOrbitFaceWalk_length K e he n

/--
[dartOrbitFaceWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma dartOrbitFaceWalk_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (dartOrbitFaceWalk K e he n).support = (List.range (n + 1)).map (fun k => dartFace ((dartNext K)^[k] e)) := by
-- proof
  apply StatMech.Lattice.dartOrbitFaceWalk_support K e he n

/--
[dartFace_iterate_mem_dartOrbitFaceWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma dartFace_iterate_mem_dartOrbitFaceWalk_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n k : ℕ}
-- given
  (he : IsBoundaryDart K e)
  (hk : k ≤ n) :
-- imply
  dartFace ((dartNext K)^[k] e) ∈ (dartOrbitFaceWalk K e he n).support := by
-- proof
  apply StatMech.Lattice.dartFace_iterate_mem_dartOrbitFaceWalk_support K e he hk

/--
[dartOrbitFaceWalk_edges_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma dartOrbitFaceWalk_edges_bdEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
  {f g : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (h : s(f, g) ∈ (dartOrbitFaceWalk K e he n).edges) :
-- imply
  bdEdge K (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.dartOrbitFaceWalk_edges_bdEdge K e he n h

/--
[dartOrbitFaceLoop_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma dartOrbitFaceLoop_length_pos_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  0 < (dartOrbitFaceLoop K hK e he).length := by
-- proof
  apply StatMech.Lattice.dartOrbitFaceLoop_length_pos K hK e he

/--
[dartOrbitFaceLoop_edges_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma dartOrbitFaceLoop_edges_bdEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {f g : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (h : s(f, g) ∈ (dartOrbitFaceLoop K hK e he).edges) :
-- imply
  bdEdge K (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.dartOrbitFaceLoop_edges_bdEdge K hK e he h

/--
[exitOrbitFaceLoop_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma exitOrbitFaceLoop_length_pos_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  0 < (exitOrbitFaceLoop (ω := ω) hfin).length := by
-- proof
  apply StatMech.Lattice.exitOrbitFaceLoop_length_pos hfin

/--
[orbitEdges_subset_bdBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma orbitEdges_subset_bdBarrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  ∀ ⦃f g : Site 2⦄, s(f, g) ∈ (dartOrbitFaceLoop K hK e he).edges → bdEdge K (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.orbitEdges_subset_bdBarrier K hK e he

/--
[orbit_separates_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma orbit_separates_origin_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (_hfin : (cluster 2 ω (origin 2)).Finite)
  (hz : z ∉ cluster 2 ω (origin 2)) :
-- imply
  ¬ (latticeMinusBarrier (cluster 2 ω (origin 2))).Reachable (origin 2) z := by
-- proof
  apply StatMech.Lattice.orbit_separates_origin _hfin hz

/--
[orbit_origin_crossCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma orbit_origin_crossCount_odd_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk (origin 2) z}
-- given
  (_hfin : (cluster 2 ω (origin 2)).Finite)
  (hz : z ∉ cluster 2 ω (origin 2)) :
-- imply
  ¬ Even (crossCount (cluster 2 ω (origin 2)) w) := by
-- proof
  apply StatMech.Lattice.orbit_origin_crossCount_odd _hfin hz w

/--
[iterate_eq_mod_of_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma iterate_eq_mod_of_period_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {f : α → α}
  {x : α}
  {p : ℕ}
  {n : ℕ}
-- given
  (hp : f^[p] x = x) :
-- imply
  f^[n] x = f^[n % p] x := by
-- proof
  apply StatMech.Lattice.iterate_eq_mod_of_period f x hp n

/--
[dartFace_iterate_mem_dartOrbitFaceLoop_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma dartFace_iterate_mem_dartOrbitFaceLoop_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  dartFace ((dartNext K)^[n] e) ∈ (dartOrbitFaceLoop K hK e he).support := by
-- proof
  apply StatMech.Lattice.dartFace_iterate_mem_dartOrbitFaceLoop_support K hK e he n

/--
[exitOrbitFaceLoop_mem_leftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma exitOrbitFaceLoop_mem_leftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : ExitDartsSameOrbit ω hfin) :
-- imply
  leftExitFaceDown (ω := ω) hfin ∈ (exitOrbitFaceLoop (ω := ω) hfin).support := by
-- proof
  apply StatMech.Lattice.exitOrbitFaceLoop_mem_leftFace hfin h

/--
[exitOrbitFaceLoop_exists_leftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma exitOrbitFaceLoop_exists_leftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : ExitDartsSameOrbit ω hfin) :
-- imply
  ∃ w ∈ (exitOrbitFaceLoop (ω := ω) hfin).support, w 0 ≤ 0 := by
-- proof
  apply StatMech.Lattice.exitOrbitFaceLoop_exists_leftFace hfin h

/--
[cycleHasLeftFace_of_canonicalOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma cycleHasLeftFace_of_canonicalOrbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : CanonicalOrbitCycle ω hfin) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Lattice.cycleHasLeftFace_of_canonicalOrbit hfin h

/--
[pcAnchoredEnclosure_of_canonicalOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma pcAnchoredEnclosure_of_canonicalOrbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), CanonicalOrbitCycle ω hfin) :
-- imply
  StatMech.Percolation.PcAnchoredEnclosure := by
-- proof
  apply StatMech.Lattice.pcAnchoredEnclosure_of_canonicalOrbit h

/--
[pc_lt_one_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitEncloses.lean)
-/
@[path]
private lemma pc_lt_one_orbit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), CanonicalOrbitCycle ω hfin) :
-- imply
  (StatMech.Percolation.pc 2 : ℝ) < 1 := by
-- proof
  apply StatMech.Lattice.pc_lt_one_orbit h


-- created on 2026-10-23
