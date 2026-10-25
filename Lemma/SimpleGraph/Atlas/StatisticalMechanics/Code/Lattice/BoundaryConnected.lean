import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[exterior_mem_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma exterior_mem_infiniteComponent_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {x : Site d}
-- given
  (hd : 2 ≤ d)
  (hR : F ⊆ box d R)
  (hx : x ∈ exterior d R) :
-- imply
  (((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨x, exterior_subset_compl F R hR hx⟩).supp.Infinite := by
-- proof
  apply StatMech.Lattice.exterior_mem_infiniteComponent hd F R hR hx

/--
[exterior_reachable_in_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma exterior_reachable_in_compl_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {x y : Site d}
-- given
  (hd : 2 ≤ d)
  (hR : F ⊆ box d R)
  (hx : x ∈ exterior d R)
  (hy : y ∈ exterior d R) :
-- imply
  ((hypercubicLattice d).induce Fᶜ).Reachable ⟨x, exterior_subset_compl F R hR hx⟩ ⟨y, exterior_subset_compl F R hR hy⟩ := by
-- proof
  apply StatMech.Lattice.exterior_reachable_in_compl hd F R hR hx hy

/--
[exterior_connectedComponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma exterior_connectedComponent_eq_eq
  {d : ℕ}
  {F : Set (Site d)}
  {R : ℕ}
  {x y : Site d}
-- given
  (hd : 2 ≤ d)
  (hR : F ⊆ box d R)
  (hx : x ∈ exterior d R)
  (hy : y ∈ exterior d R) :
-- imply
  ((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨x, exterior_subset_compl F R hR hx⟩ = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk ⟨y, exterior_subset_compl F R hR hy⟩ := by
-- proof
  apply StatMech.Lattice.exterior_connectedComponent_eq hd F R hR hx hy

/--
[clusterComplement_unique_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma clusterComplement_unique_infiniteComponent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃! C : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).ConnectedComponent, C.supp.Infinite := by
-- proof
  apply StatMech.Lattice.clusterComplement_unique_infiniteComponent hfin

/--
[exists_clusterBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma exists_clusterBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R := by
-- proof
  apply StatMech.Lattice.exists_clusterBox hfin

/--
[axisFarRight_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma axisFarRight_mem_exterior_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ} :
-- imply
  (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.axisFarRight_mem_exterior R

/--
[axisFarLeft_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma axisFarLeft_mem_exterior_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ} :
-- imply
  (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.axisFarLeft_mem_exterior R

/--
[axisFar_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma axisFar_sameComponent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk ⟨![(R : ℤ) + 1, 0], exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩ = ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk ⟨![-((R : ℤ) + 1), 0], exterior_subset_compl _ R hR (axisFarLeft_mem_exterior R)⟩ := by
-- proof
  apply StatMech.Lattice.axisFar_sameComponent R hR

/--
[axisFar_reachable_in_clusterComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma axisFar_reachable_in_clusterComplement_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨![(R : ℤ) + 1, 0], exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩ ⟨![-((R : ℤ) + 1), 0], exterior_subset_compl _ R hR (axisFarLeft_mem_exterior R)⟩ := by
-- proof
  apply StatMech.Lattice.axisFar_reachable_in_clusterComplement R hR

/--
[axisFarRight_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma axisFarRight_infiniteComponent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
-- imply
  (((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk ⟨![(R : ℤ) + 1, 0], exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩).supp.Infinite := by
-- proof
  apply StatMech.Lattice.axisFarRight_infiniteComponent R hR

/--
[cycleHasLeftFace_of_enclosingContourLinksExits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma cycleHasLeftFace_of_enclosingContourLinksExits_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : EnclosingContourLinksExits ω hfin) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Lattice.cycleHasLeftFace_of_enclosingContourLinksExits hfin h

/--
[anchoredCycleExists_of_enclosingContourLinksExits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma anchoredCycleExists_of_enclosingContourLinksExits_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : EnclosingContourLinksExits ω hfin) :
-- imply
  AnchoredCycleExists ω hfin := by
-- proof
  apply StatMech.Lattice.anchoredCycleExists_of_enclosingContourLinksExits hfin h

/--
[pcAnchoredEnclosure_of_enclosingContourLinksExits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma pcAnchoredEnclosure_of_enclosingContourLinksExits_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.PcAnchoredEnclosure := by
-- proof
  apply StatMech.Lattice.pcAnchoredEnclosure_of_enclosingContourLinksExits h

/--
[pc_lt_one_via_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean)
-/
@[path]
private lemma pc_lt_one_via_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.pc_lt_one_via_boundary h


-- created on 2026-10-23
