import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bmm_cluster_omegaClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean)
-/
@[path]
private lemma bmm_cluster_omegaClosed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  ∀ u v, u ∈ cluster d ω x → IsOpenEdge d ω u v → v ∈ cluster d ω x := by
-- proof
  apply StatMech.Percolation.bmm_cluster_omegaClosed ω x

/--
[bmm_regions_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean)
-/
@[path]
private lemma bmm_regions_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hxy : cluster d ω x ≠ cluster d ω y) :
-- imply
  Disjoint (cluster d ω x) (cluster d ω y) := by
-- proof
  apply StatMech.Percolation.bmm_regions_disjoint ω hxy

/--
[bmm_distinct_neighbours_of_disjoint_regions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean)
-/
@[path]
private lemma bmm_distinct_neighbours_of_disjoint_regions_eq
  {d : ℕ}
  {a b : Site d}
  {R S : Set (Site d)}
-- given
  (ha : a ∈ R)
  (hb : b ∈ S)
  (hdisj : Disjoint R S) :
-- imply
  a ≠ b := by
-- proof
  apply StatMech.Percolation.bmm_distinct_neighbours_of_disjoint_regions ha hb hdisj

/--
[bmm_boxMergeFreeInsertion_of_attachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean)
-/
@[path]
private lemma bmm_boxMergeFreeInsertion_of_attachment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bmm_BoxMengerAttachment d n) :
-- imply
  tre_BoxMergeFreeInsertion d n := by
-- proof
  apply StatMech.Percolation.bmm_boxMergeFreeInsertion_of_attachment h

/--
[bmm_threeClustersReachOrigin_of_attachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean)
-/
@[path]
private lemma bmm_threeClustersReachOrigin_of_attachment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bmm_BoxMengerAttachment d n) :
-- imply
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.bmm_threeClustersReachOrigin_of_attachment h

/--
[bmm_disjointRouting_of_attachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean)
-/
@[path]
private lemma bmm_disjointRouting_of_attachment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bmm_BoxMengerAttachment d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.bmm_disjointRouting_of_attachment h

/--
[bmm_attachment_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMergeFreeMenger.lean)
-/
@[path]
private lemma bmm_attachment_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))), ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃) ∧ (∀ e ∈ W, (0 : Site d) ∉ e) ∧ (a₁ ∈ cluster d ω x₁ ∧ a₂ ∈ cluster d ω x₂ ∧ a₃ ∈ cluster d ω x₃) ∧ ((∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁) ∧ (∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂) ∧ (∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)) ∧ (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧ Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧ Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧ ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) := by
-- proof
  apply StatMech.Percolation.bmm_attachment_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri


-- created on 2026-10-23
