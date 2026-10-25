import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.AxisAssignmentClose.Part2
open MeasureTheory Set Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[caa_axisAssignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_axisAssignment_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Fin 3 → Site d}
  {S : Fin 3 → Finset (Fin d)}
-- given
  (h : caa_RunsAlongCandidates ω x S) :
-- imply
  ∃ f : Fin 3 → Fin d, Function.Injective f ∧ ∀ i : Fin 3, crr_ClusterRunsAlongAxis ω (x i) (f i) := by
-- proof
  apply StatMech.Percolation.caa_axisAssignment ω x S h

/--
[caa_three_reachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_three_reachesRay_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Fin 3 → Site d}
  {S : Fin 3 → Finset (Fin d)}
-- given
  (h : caa_RunsAlongCandidates ω x S) :
-- imply
  ∃ j : Fin 3 → Fin d, (j 0 ≠ j 1 ∧ j 0 ≠ j 2 ∧ j 1 ≠ j 2) ∧ (∀ i : Fin 3, lma_ClusterReachesRay ω (x i) (j i)) := by
-- proof
  apply StatMech.Percolation.caa_three_reachesRay ω x S h

/--
[caa_hall_of_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_hall_of_full_eq
  {d : ℕ}
  {S : Fin 3 → Finset (Fin d)}
-- given
  (hd : 3 ≤ d)
  (hfull : ∀ i, S i = Finset.univ) :
-- imply
  ∀ s : Finset (Fin 3), s.card ≤ (s.biUnion S).card := by
-- proof
  apply StatMech.Percolation.caa_hall_of_full hd S hfull

/--
[caa_hall_of_injective_singletons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_hall_of_injective_singletons_eq
  {d : ℕ}
  {a : Fin 3 → Fin d}
-- given
  (ha : Function.Injective a) :
-- imply
  ∀ s : Finset (Fin 3), s.card ≤ (s.biUnion (fun i => ({a i} : Finset (Fin d)))).card := by
-- proof
  apply StatMech.Percolation.caa_hall_of_injective_singletons a ha

/--
[caa_attachData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_attachData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {S : Fin 3 → Finset (Fin d)}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Percolation.caa_attachData ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 h

/--
[caa_threeClustersReachOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_threeClustersReachOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {S : Fin 3 → Finset (Fin d)}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.caa_threeClustersReachOrigin ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 h

/--
[caa_boxClusterReachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_boxClusterReachesRay_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : caa_BoxRunsAlongCandidates d n) :
-- imply
  lma_BoxClusterReachesRay d n := by
-- proof
  apply StatMech.Percolation.caa_boxClusterReachesRay h

/--
[caa_disjointRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_disjointRouting_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : caa_BoxRunsAlongCandidates d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.caa_disjointRouting h

/--
[caa_candidates_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_candidates_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Fin 3 → Fin d}
-- given
  (ha : Function.Injective a)
  (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
-- imply
  caa_RunsAlongCandidates ω (fun i => hrHD_rayPt (a i) 1) (fun i => ({a i} : Finset (Fin d))) := by
-- proof
  apply StatMech.Percolation.caa_candidates_neighbour_witnesses ω a ha hinf

/--
[caa_nonvacuous_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean)
-/
@[path]
private lemma caa_nonvacuous_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Fin 3 → Fin d}
-- given
  (ha : Function.Injective a)
  (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
-- imply
  (∃ j : Fin 3 → Fin d, (j 0 ≠ j 1 ∧ j 0 ≠ j 2 ∧ j 1 ≠ j 2) ∧ (∀ i : Fin 3, lma_ClusterReachesRay ω (hrHD_rayPt (a i) 1) (j i))) ∧ (hrHD_rayPt (a 0) 1 ≠ hrHD_rayPt (a 1) 1 ∧ hrHD_rayPt (a 0) 1 ≠ hrHD_rayPt (a 2) 1 ∧ hrHD_rayPt (a 1) 1 ≠ hrHD_rayPt (a 2) 1) := by
-- proof
  apply StatMech.Percolation.caa_nonvacuous_neighbour_witnesses ω a ha hinf


-- created on 2026-10-23
