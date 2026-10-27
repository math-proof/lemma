import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc15core.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc15_runsAlongAxis_of_nearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_runsAlongAxis_of_nearReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc15_NearAxisReach ω x j) :
-- imply
  crr_ClusterRunsAlongAxis ω x j := by
-- proof
  apply StatMech.Walls.bc15_runsAlongAxis_of_nearReach ω x j h

/--
[bc15_nearReach_of_runsAlongAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_nearReach_of_runsAlongAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  bc15_NearAxisReach ω x j := by
-- proof
  apply StatMech.Walls.bc15_nearReach_of_runsAlongAxis ω x j h

/--
[bc15_runsAlong_iff_nearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_runsAlong_iff_nearReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d} :
-- imply
  crr_ClusterRunsAlongAxis ω x j ↔ bc15_NearAxisReach ω x j := by
-- proof
  apply StatMech.Walls.bc15_runsAlong_iff_nearReach ω x j

/--
[bc15_connected_of_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_connected_of_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : Connected d (removeSite 0 ω) x (hrHD_rayPt j 1)) :
-- imply
  Connected d ω x (hrHD_rayPt j 1) := by
-- proof
  apply StatMech.Walls.bc15_connected_of_cut ω x j h

/--
[bc15_nearReach_of_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_nearReach_of_cutNearReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc15_CutNearReach ω x j) :
-- imply
  bc15_NearAxisReach ω x j := by
-- proof
  apply StatMech.Walls.bc15_nearReach_of_cutNearReach ω x j h

/--
[bc15_cutNearReach_of_nearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_cutNearReach_of_nearReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc15_NearAxisReach ω x j) :
-- imply
  bc15_CutNearReach ω x j := by
-- proof
  apply StatMech.Walls.bc15_cutNearReach_of_nearReach ω x j h

/--
[bc15_runsAlong_iff_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_runsAlong_iff_cutNearReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d} :
-- imply
  crr_ClusterRunsAlongAxis ω x j ↔ bc15_CutNearReach ω x j := by
-- proof
  apply StatMech.Walls.bc15_runsAlong_iff_cutNearReach ω x j

/--
[bc15_runsAlongAxis_of_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_runsAlongAxis_of_cutNearReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc15_CutNearReach ω x j) :
-- imply
  crr_ClusterRunsAlongAxis ω x j := by
-- proof
  apply StatMech.Walls.bc15_runsAlongAxis_of_cutNearReach ω x j h

/--
[bc15_boxClusterRunsAlong_of_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_boxClusterRunsAlong_of_cutNearReach_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc15_BoxClusterCutNearReach d n) :
-- imply
  bc14_BoxClusterRunsAlongAxis d n := by
-- proof
  apply StatMech.Walls.bc15_boxClusterRunsAlong_of_cutNearReach h

/--
[bc15_boxClusterReachesRay_of_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_boxClusterReachesRay_of_cutNearReach_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc15_BoxClusterCutNearReach d n) :
-- imply
  lma_BoxClusterReachesRay d n := by
-- proof
  apply StatMech.Walls.bc15_boxClusterReachesRay_of_cutNearReach h

/--
[bc15_hroute_of_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_hroute_of_cutNearReach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hreach : ∀ n : ℕ, bc15_BoxClusterCutNearReach d n) :
-- imply
  ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc15_hroute_of_cutNearReach μ hfe hreach

/--
[bc15_burton_keane_uniqueness_of_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_burton_keane_uniqueness_of_cutNearReach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hreach : ∀ n : ℕ, bc15_BoxClusterCutNearReach d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc15_burton_keane_uniqueness_of_cutNearReach μ herg hfe bdry hbound hvol hdens hreach

/--
[bc15_cutNearReach_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_cutNearReach_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  bc15_CutNearReach ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Walls.bc15_cutNearReach_neighbour ω j hinf

/--
[bc15_runsAlong_neighbour_of_cutNearReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_runsAlong_neighbour_of_cutNearReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Walls.bc15_runsAlong_neighbour_of_cutNearReach ω j hinf

/--
[bc15_cutNearReach_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_cutNearReach_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  ∃ j' : Fin d, bc15_CutNearReach ω (hrHD_rayPt j 1) j' := by
-- proof
  apply StatMech.Walls.bc15_cutNearReach_nonvacuous ω j hinf

/--
[bc15_cutReach_far_record](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean)
-/
@[path]
private lemma bc15_cutReach_far_record_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc15_cutReach_far_record ω x hinf n


-- created on 2026-10-23
