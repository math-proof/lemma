import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ClusterAttachment.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[cla_walk_survival_force](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_walk_survival_force_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d ω).Walk a x}
-- given
  (hw : (0 : Site d) ∉ w.support) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset W ω)) a x := by
-- proof
  apply StatMech.Percolation.cla_walk_survival_force ω W w hw

/--
[cla_walk_survival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_walk_survival_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d ω).Walk a x}
-- given
  (hw : (0 : Site d) ∉ w.support) :
-- imply
  Connected d (removeSite 0 ω) a x := by
-- proof
  apply StatMech.Percolation.cla_walk_survival ω w hw

/--
[cla_clusterAttachment_of_avoidingWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_clusterAttachment_of_avoidingWalk_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d ω).Walk a x}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a)
  (hmem : a ∈ cluster d ω x)
  (hw : (0 : Site d) ∉ w.support)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  bma_ClusterAttachment ω x := by
-- proof
  apply StatMech.Percolation.cla_clusterAttachment_of_avoidingWalk ω hadj hmem w hw hri

/--
[cla_clusterAttachment_of_avoidingAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_clusterAttachment_of_avoidingAttachment_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : cla_AvoidingAttachment ω x) :
-- imply
  bma_ClusterAttachment ω x := by
-- proof
  apply StatMech.Percolation.cla_clusterAttachment_of_avoidingAttachment ω x h

/--
[cla_avoidingAttachment_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_avoidingAttachment_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  cla_AvoidingAttachment ω x := by
-- proof
  apply StatMech.Percolation.cla_avoidingAttachment_of_neighbour ω x hadj hri

/--
[cla_clusterAttachment_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_clusterAttachment_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  bma_ClusterAttachment ω x := by
-- proof
  apply StatMech.Percolation.cla_clusterAttachment_of_neighbour ω x hadj hri

/--
[cla_boxClusterAttachment_of_boxAvoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_boxClusterAttachment_of_boxAvoiding_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : cla_BoxAvoidingAttachment d n) :
-- imply
  bma_BoxClusterAttachment d n := by
-- proof
  apply StatMech.Percolation.cla_boxClusterAttachment_of_boxAvoiding h

/--
[cla_boxMengerAttachment_of_boxAvoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_boxMengerAttachment_of_boxAvoiding_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : cla_BoxAvoidingAttachment d n) :
-- imply
  bmm_BoxMengerAttachment d n := by
-- proof
  apply StatMech.Percolation.cla_boxMengerAttachment_of_boxAvoiding h

/--
[cla_disjointRouting_of_boxAvoiding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_disjointRouting_of_boxAvoiding_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : cla_BoxAvoidingAttachment d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.cla_disjointRouting_of_boxAvoiding h

/--
[cla_three_avoidingAttachments_of_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterAttachment.lean)
-/
@[path]
private lemma cla_three_avoidingAttachments_of_neighbours_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  cla_AvoidingAttachment ω x₁ ∧ cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃ := by
-- proof
  apply StatMech.Percolation.cla_three_avoidingAttachments_of_neighbours ω x₁ x₂ x₃ hadj hri


-- created on 2026-10-23
