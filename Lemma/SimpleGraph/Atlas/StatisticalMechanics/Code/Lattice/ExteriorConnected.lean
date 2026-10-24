import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.ExteriorConnected
open Set SimpleGraph StatMech StatMech.Lattice


/--
[exc_unitCell_offK_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_unitCell_offK_on_support_eq :
-- imply
  (![0, -1] : Site 2) ∈ (mpl_orbitLoop unitCell ucBase).support := by
-- proof
  apply StatMech.Lattice.exc_unitCell_offK_on_support

/--
[exc_unitCell_offK_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_unitCell_offK_notMem_eq :
-- imply
  (![0, -1] : Site 2) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.exc_unitCell_offK_notMem

/--
[exc_oldExteriorConnected_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_oldExteriorConnected_false_eq :
-- imply
  ¬ ior_ExteriorConnected unitCell ucBase := by
-- proof
  apply StatMech.Lattice.exc_oldExteriorConnected_false

/--
[exc_reachable_compl_to_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_reachable_compl_to_offSupport_walk_eq
  {F : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ Fᶜ)
  (hy : y ∈ Fᶜ)
  (h : ((hypercubicLattice 2).induce Fᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ w ∈ p.support, w ∉ F := by
-- proof
  apply StatMech.Lattice.exc_reachable_compl_to_offSupport_walk F hx hy h

/--
[exc_farLeft_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_farLeft_mem_exterior_eq
  {R : ℕ} :
-- imply
  (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.exc_farLeft_mem_exterior R

/--
[exc_exterior_reaches_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_exterior_reaches_farLeft_eq
  {F : Set (Site 2)}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : F ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ F) ∧ (∀ q ∈ F, z0 0 ≤ q 0) := by
-- proof
  apply StatMech.Lattice.exc_exterior_reaches_farLeft F R hR z hz

/--
[exc_loopSupport_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_loopSupport_finite_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)).Finite := by
-- proof
  apply StatMech.Lattice.exc_loopSupport_finite K a

/--
[exc_exists_loopSupportBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_exists_loopSupportBox_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ∃ R : ℕ, ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R := by
-- proof
  apply StatMech.Lattice.exc_exists_loopSupportBox K a

/--
[exc_offSupport_of_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_offSupport_of_reaches_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : exc_OffSupportReachesExterior K a) :
-- imply
  ∀ z, z ∉ K → z ∉ (mpl_orbitLoop K a).support → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) := by
-- proof
  apply StatMech.Lattice.exc_offSupport_of_reaches K a h

/--
[exc_interiorSubset_of_reaches_and_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_interiorSubset_of_reaches_and_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Lattice.exc_interiorSubset_of_reaches_and_support K a hoff hsupp

/--
[exc_unitCell_supportOddInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_unitCell_supportOddInK_eq :
-- imply
  exc_SupportOddInK unitCell ucBase := by
-- proof
  apply StatMech.Lattice.exc_unitCell_supportOddInK

/--
[exc_exterior_self_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnected.lean)
-/
@[path]
private lemma exc_exterior_self_reachable_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ((hypercubicLattice 2).induce ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable ⟨z, exterior_subset_compl _ R hR hz⟩ ⟨z, exterior_subset_compl _ R hR hz⟩ := by
-- proof
  apply StatMech.Lattice.exc_exterior_self_reachable K a R hR z hz


-- created on 2026-10-23
