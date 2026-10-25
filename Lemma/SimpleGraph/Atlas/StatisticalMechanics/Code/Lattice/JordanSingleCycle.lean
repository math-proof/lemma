import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
open Finset Set SimpleGraph Function List StatMech StatMech.Lattice


/--
[polygon_edges_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma polygon_edges_nodup_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {g : ℕ → V}
  {p : ℕ}
-- given
  (hp : 3 ≤ p)
  (hper : ∀ k, g k = g (k % p))
  (hinj : Set.InjOn g (Set.Iio p)) :
-- imply
  ((List.range p).map (fun k => s(g k, g (k + 1)))).Nodup := by
-- proof
  apply StatMech.Lattice.polygon_edges_nodup g p hp hper hinj

/--
[polygon_support_tail_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma polygon_support_tail_nodup_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {g : ℕ → V}
  {p : ℕ}
-- given
  (hp : 1 ≤ p)
  (hper : ∀ k, g k = g (k % p))
  (hinj : Set.InjOn g (Set.Iio p)) :
-- imply
  (((List.range (p + 1)).map g).tail).Nodup := by
-- proof
  apply StatMech.Lattice.polygon_support_tail_nodup g p hp hper hinj

/--
[orbitFaceWalk_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma orbitFaceWalk_edges_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (dartOrbitFaceWalk K e he n).edges = (List.range n).map (fun k => s(dartFace ((dartNext K)^[k] e), dartFace ((dartNext K)^[k + 1] e))) := by
-- proof
  apply StatMech.Lattice.orbitFaceWalk_edges K e he n

/--
[orbitFaceWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma orbitFaceWalk_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ p)
  (hcl : (dartNext K)^[p] e = e)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio p)) :
-- imply
  ((dartOrbitFaceWalk K e he p).copy rfl (by rw [hcl])).IsCycle := by
-- proof
  apply StatMech.Lattice.orbitFaceWalk_isCycle K e he p hp hcl hinj

/--
[exit_period_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma exit_period_closure_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (dartNext (cluster 2 ω (origin 2)))^[dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)] (exitDart (ω := ω) hfin) = exitDart (ω := ω) hfin := by
-- proof
  apply StatMech.Lattice.exit_period_closure hfin

/--
[exitMinFaceLoop_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma exitMinFaceLoop_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (exitMinFaceLoop (ω := ω) hfin).support = (List.range (dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) + 1)).map (fun k => dartFace ((dartNext (cluster 2 ω (origin 2)))^[k] (exitDart (ω := ω) hfin))) := by
-- proof
  apply StatMech.Lattice.exitMinFaceLoop_support hfin

/--
[exitMinFaceLoop_mem_leftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma exitMinFaceLoop_mem_leftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : ExitDartsSameOrbit ω hfin) :
-- imply
  leftExitFaceDown (ω := ω) hfin ∈ (exitMinFaceLoop (ω := ω) hfin).support := by
-- proof
  apply StatMech.Lattice.exitMinFaceLoop_mem_leftFace hfin h

/--
[exitMinFaceLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma exitMinFaceLoop_isCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : OrbitFaceSimple ω hfin) :
-- imply
  (exitMinFaceLoop (ω := ω) hfin).IsCycle := by
-- proof
  apply StatMech.Lattice.exitMinFaceLoop_isCycle hfin h

/--
[cycleHasLeftFace_of_orbitFaceSimple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma cycleHasLeftFace_of_orbitFaceSimple_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsimple : OrbitFaceSimple ω hfin)
  (hsame : ExitDartsSameOrbit ω hfin) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Lattice.cycleHasLeftFace_of_orbitFaceSimple hfin hsimple hsame

/--
[pcAnchoredEnclosure_of_orbitFaceSimple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma pcAnchoredEnclosure_of_orbitFaceSimple_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), OrbitFaceSimple ω hfin ∧ ExitDartsSameOrbit ω hfin) :
-- imply
  StatMech.Percolation.PcAnchoredEnclosure := by
-- proof
  apply StatMech.Lattice.pcAnchoredEnclosure_of_orbitFaceSimple h

/--
[pc_lt_one_of_orbitFaceSimple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean)
-/
@[path]
private lemma pc_lt_one_of_orbitFaceSimple_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), OrbitFaceSimple ω hfin ∧ ExitDartsSameOrbit ω hfin) :
-- imply
  (StatMech.Percolation.pc 2 : ℝ) < 1 := by
-- proof
  apply StatMech.Lattice.pc_lt_one_of_orbitFaceSimple h


-- created on 2026-10-23
