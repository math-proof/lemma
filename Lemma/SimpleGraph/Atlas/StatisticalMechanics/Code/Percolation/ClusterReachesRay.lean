import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[crr_infinite_reaches_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_infinite_reaches_far_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ y, y ∉ box d n ∧ Connected d ω x y := by
-- proof
  apply StatMech.Percolation.crr_infinite_reaches_far ω x hinf n

/--
[crr_infinite_reaches_far_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_infinite_reaches_far_coord_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y := by
-- proof
  apply StatMech.Percolation.crr_infinite_reaches_far_coord ω x hinf n

/--
[crr_removeSite_infinite_reaches_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_removeSite_infinite_reaches_far_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Percolation.crr_removeSite_infinite_reaches_far ω x hinf n

/--
[crr_axisOpen_connected_in](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_axisOpen_connected_in_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true)
  (hm : m ≤ L) :
-- imply
  Connected d ω (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
-- proof
  apply StatMech.Percolation.crr_axisOpen_connected_in ω j L hopen m hm

/--
[crr_axisOpen_connected_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_axisOpen_connected_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true)
  (hm : m ≤ L) :
-- imply
  Connected d (removeSite 0 ω) (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
-- proof
  apply StatMech.Percolation.crr_axisOpen_connected_removeSite ω j L hopen m hm

/--
[crr_corridor_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_corridor_internal_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (hxe1 : Connected d ω x (hrHD_rayPt j 1))
  (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) :
-- imply
  ∀ e ∈ lma_corridorEdges j L, ∀ p, p ∈ e → p ∈ cluster d ω x := by
-- proof
  apply StatMech.Percolation.crr_corridor_internal ω x j L hxe1 hopen

/--
[crr_clusterReachesRay_of_runsAlongAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_clusterReachesRay_of_runsAlongAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  lma_ClusterReachesRay ω x j := by
-- proof
  apply StatMech.Percolation.crr_clusterReachesRay_of_runsAlongAxis ω x j h

/--
[crr_runsAlongAxis_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_runsAlongAxis_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Percolation.crr_runsAlongAxis_of_neighbour ω j hinf

/--
[crr_clusterReachesRay_of_neighbour'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_clusterReachesRay_of_neighbour'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  lma_ClusterReachesRay ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Percolation.crr_clusterReachesRay_of_neighbour' ω j hinf

/--
[crr_clusterReachesRay_of_assignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean)
-/
@[path]
private lemma crr_clusterReachesRay_of_assignment_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : crr_AxisAssignment ω x j) :
-- imply
  lma_ClusterReachesRay ω x j := by
-- proof
  apply StatMech.Percolation.crr_clusterReachesRay_of_assignment ω x j h


-- created on 2026-10-23
