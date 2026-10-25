import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tre_removeSite_forceOpen_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_removeSite_forceOpen_comm_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hW : ∀ e ∈ W, (0 : Site d) ∉ e) :
-- imply
  removeSite 0 (forceOpenFinset W ω) = forceOpenFinset W (removeSite 0 ω) := by
-- proof
  apply StatMech.Percolation.tre_removeSite_forceOpen_comm W hW ω

/--
[tre_removeSite_mono_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_removeSite_mono_forceOpen_eq
  {d : ℕ}
  {W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hW : ∀ e ∈ W, (0 : Site d) ∉ e) :
-- imply
  removeSite 0 ω ≤ removeSite 0 (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tre_removeSite_mono_forceOpen W hW ω

/--
[tre_cluster_infinite_of_omega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_cluster_infinite_of_omega_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {x : Site d}
-- given
  (hW : ∀ e ∈ W, (0 : Site d) ∉ e)
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  (cluster d (removeSite 0 (forceOpenFinset W ω)) x).Infinite := by
-- proof
  apply StatMech.Percolation.tre_cluster_infinite_of_omega ω W hW x hinf

/--
[tre_branch_infinite_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_branch_infinite_of_reach_eq
  {d : ℕ}
  {ω' : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
-- given
  (hc : Connected d (removeSite 0 ω') a x)
  (hinf : (cluster d (removeSite 0 ω') x).Infinite) :
-- imply
  (cluster d (removeSite 0 ω') a).Infinite := by
-- proof
  apply StatMech.Percolation.tre_branch_infinite_of_reach ω' a x hc hinf

/--
[tre_branch_distinct_of_regions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_branch_distinct_of_regions_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {a b : Site d}
  {R S : Set (Site d)}
-- given
  (haR : a ∈ R)
  (hbS : b ∈ S)
  (homR : ∀ u v, u ∈ R → IsOpenEdge d ω u v → v ∈ R)
  (hgR : ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R)
  (homS : ∀ u v, u ∈ S → IsOpenEdge d ω u v → v ∈ S)
  (hgS : ∀ u v, u ∈ S → s(u, v) ∈ W → v ∈ S)
  (hdisj : Disjoint R S) :
-- imply
  cluster d (removeSite 0 (forceOpenFinset W ω)) a ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) b := by
-- proof
  apply StatMech.Percolation.tre_branch_distinct_of_regions ω W a b R S haR hbS homR hgR homS hgS hdisj

/--
[tre_threeClustersReachOrigin_of_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_threeClustersReachOrigin_of_insertion_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : tre_MergeFreeInsertion ω) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tre_threeClustersReachOrigin_of_insertion ω h

/--
[tre_mergeFree_of_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_mergeFree_of_insertion_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : tre_MergeFreeInsertion ω) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), bka_MergeFree (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tre_mergeFree_of_insertion ω h

/--
[tre_insertion_of_boxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_insertion_of_boxResidue_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : tre_BoxMergeFreeInsertion d n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  tre_MergeFreeInsertion ω := by
-- proof
  apply StatMech.Percolation.tre_insertion_of_boxResidue h hω

/--
[tre_threeClustersReachOrigin_of_finiteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_threeClustersReachOrigin_of_finiteEnergy_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : tre_BoxMergeFreeInsertion d n) :
-- imply
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tre_threeClustersReachOrigin_of_finiteEnergy h

/--
[tre_forceOpenFinset_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_forceOpenFinset_comp_eq
  {d : ℕ}
  {F W : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  forceOpenFinset F (forceOpenFinset W ω) = forceOpenFinset (F ∪ W) ω := by
-- proof
  apply StatMech.Percolation.tre_forceOpenFinset_comp F W ω

/--
[tre_precursor_of_modifiedMergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_precursor_of_modifiedMergeFree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
-- given
  (h : bka_MergeFree (forceOpenFinset W ω)) :
-- imply
  ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d), forceOpenFinset G ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃ := by
-- proof
  apply StatMech.Percolation.tre_precursor_of_modifiedMergeFree ω W h

/--
[tre_disjointRouting_of_finiteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_disjointRouting_of_finiteEnergy_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : tre_BoxMergeFreeInsertion d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.tre_disjointRouting_of_finiteEnergy h

/--
[tre_threeClustersReachOrigin_of_insertionRho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_threeClustersReachOrigin_of_insertionRho_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : tre_MergeFreeInsertionRho ω) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tre_threeClustersReachOrigin_of_insertionRho ω h

/--
[tre_mergeFreeInsertionRho_of_reachOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean)
-/
@[path]
private lemma tre_mergeFreeInsertionRho_of_reachOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω) :
-- imply
  tre_MergeFreeInsertionRho ω := by
-- proof
  apply StatMech.Percolation.tre_mergeFreeInsertionRho_of_reachOrigin ω h


-- created on 2026-10-23
