import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc56menger.Part4
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc56_clusterAttachment_of_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_clusterAttachment_of_reachesNbr_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : bc56_ClusterReachesNbr ω x) :
-- imply
  bma_ClusterAttachment ω x := by
-- proof
  apply StatMech.Walls.bc56_clusterAttachment_of_reachesNbr ω x h

/--
[bc56_boxClusterAttachment_of_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_boxClusterAttachment_of_reachesNbr_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc56_BoxClusterReachesNbr d n) :
-- imply
  bma_BoxClusterAttachment d n := by
-- proof
  apply StatMech.Walls.bc56_boxClusterAttachment_of_reachesNbr h

/--
[bc56_boxMengerAttachment_of_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_boxMengerAttachment_of_reachesNbr_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc56_BoxClusterReachesNbr d n) :
-- imply
  bmm_BoxMengerAttachment d n := by
-- proof
  apply StatMech.Walls.bc56_boxMengerAttachment_of_reachesNbr h

/--
[bc56_burton_keane_bernoulli_of_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_burton_keane_bernoulli_of_reachesNbr_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc56_burton_keane_bernoulli_of_reachesNbr hd p hp1 hp0 h

/--
[bc56_reachesNbr_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_reachesNbr_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x)
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  bc56_ClusterReachesNbr ω x := by
-- proof
  apply StatMech.Walls.bc56_reachesNbr_of_neighbour ω x hadj hinf

/--
[bc56_threeRayConfig_reachesNbr_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_threeRayConfig_reachesNbr_witness_eq
  {d : ℕ} :
-- imply
  bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) ∧ bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px (-1)) ∧ bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.py 1) := by
-- proof
  apply StatMech.Walls.bc56_threeRayConfig_reachesNbr_witness

/--
[bc56_runsAlongAxis_forces_nbr_in_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_runsAlongAxis_forces_nbr_in_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  hrHD_rayPt j 1 ∈ cluster d ω x := by
-- proof
  apply StatMech.Walls.bc56_runsAlongAxis_forces_nbr_in_cluster ω x j h

/--
[bc56_lp_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_lp_inj_eq
  {d : ℕ} :
-- imply
  Function.Injective bc56_lp := by
-- proof
  apply StatMech.Walls.bc56_lp_inj

/--
[bc56_lp_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_lp_snd_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  (bc56_lp k) 1 = 2 := by
-- proof
  apply StatMech.Walls.bc56_lp_snd k

/--
[bc56_lp_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_lp_adj_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (bc56_lp k) (bc56_lp (k + 1)) := by
-- proof
  apply StatMech.Walls.bc56_lp_adj k

/--
[bc56_offAxisLine_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_offAxisLine_open_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  bc56_offAxisLine s(bc56_lp k, bc56_lp (k + 1)) = true := by
-- proof
  apply StatMech.Walls.bc56_offAxisLine_open k

/--
[bc56_offAxisLine_connected_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_offAxisLine_connected_pos_eq
  {d : ℕ}
  {m : ℤ}
-- given
  (hm : 0 ≤ m) :
-- imply
  Connected 2 bc56_offAxisLine (bc56_lp 0) (bc56_lp m) := by
-- proof
  apply StatMech.Walls.bc56_offAxisLine_connected_pos m hm

/--
[bc56_lp_pos_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_lp_pos_outside_box_eq
  {d : ℕ}
  {m : ℕ} :
-- imply
  bc56_lp (m + 1) ∉ box 2 m := by
-- proof
  apply StatMech.Walls.bc56_lp_pos_outside_box m

/--
[bc56_offAxisLine_cluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_offAxisLine_cluster_infinite_eq
  {d : ℕ} :
-- imply
  (cluster 2 bc56_offAxisLine (bc56_lp 0)).Infinite := by
-- proof
  apply StatMech.Walls.bc56_offAxisLine_cluster_infinite

/--
[bc56_lp_zero_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_lp_zero_mem_box_eq
  {d : ℕ} :
-- imply
  bc56_lp 0 ∈ box 2 2 := by
-- proof
  apply StatMech.Walls.bc56_lp_zero_mem_box

/--
[bc56_offAxisLine_height_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_offAxisLine_height_step_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (_hu : u 1 = 2)
  (hadj : (openSubgraph 2 bc56_offAxisLine).Adj u v) :
-- imply
  v 1 = 2 := by
-- proof
  apply StatMech.Walls.bc56_offAxisLine_height_step _hu hadj

/--
[bc56_offAxisLine_height_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_offAxisLine_height_invariant_eq
  {d : ℕ}
  {u y : Site 2}
-- given
  (hu : u 1 = 2)
  (h : Connected 2 bc56_offAxisLine u y) :
-- imply
  y 1 = 2 := by
-- proof
  apply StatMech.Walls.bc56_offAxisLine_height_invariant hu h

/--
[bc56_offAxisLine_no_originNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_offAxisLine_no_originNbr_eq
  {d : ℕ} :
-- imply
  ∀ a : Site 2, (hypercubicLattice 2).Adj 0 a → a ∉ cluster 2 bc56_offAxisLine (bc56_lp 0) := by
-- proof
  apply StatMech.Walls.bc56_offAxisLine_no_originNbr

/--
[bc56_offAxisLine_no_runsAlongAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_offAxisLine_no_runsAlongAxis_eq
  {d : ℕ}
  {j : Fin 2} :
-- imply
  ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j := by
-- proof
  apply StatMech.Walls.bc56_offAxisLine_no_runsAlongAxis j

/--
[bc56_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean)
-/
@[path]
private lemma bc56_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  ((∀ n : ℕ, bc56_BoxClusterReachesNbr d n) → bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0) ∧ (∀ j : Fin 2, ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j) := by
-- proof
  apply StatMech.Walls.bc56_status hd p hp1 hp0


-- created on 2026-10-23
