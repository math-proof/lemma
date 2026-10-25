import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.InteriorOrientation.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ior_rayCount_eq_zero_of_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_rayCount_eq_zero_of_farLeft_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
-- imply
  jec_rayCount z (mpl_orbitLoop K a) = 0 := by
-- proof
  apply StatMech.Lattice.ior_rayCount_eq_zero_of_farLeft K a z hfar

/--
[ior_farLeft_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_farLeft_even_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Lattice.ior_farLeft_even K a z hfar

/--
[ior_exterior_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_exterior_even_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z z0 : Site 2}
  {p : (hypercubicLattice 2).Walk z z0}
-- given
  (hp : ∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)
  (hfar : ∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Lattice.ior_exterior_even K a p hp hfar

/--
[ior_InteriorSubset_of_exteriorConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_InteriorSubset_of_exteriorConnected_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hext : ior_ExteriorConnected K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Lattice.ior_InteriorSubset_of_exteriorConnected K a hext

/--
[ior_unitCell_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_unitCell_interiorSubset_eq :
-- imply
  eaw_InteriorSubset unitCell ucBase := by
-- proof
  apply StatMech.Lattice.ior_unitCell_interiorSubset

/--
[ior_interiorSubset_iff_leftRegion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_interiorSubset_iff_leftRegion_subset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  eaw_InteriorSubset K a ↔ jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
-- proof
  apply StatMech.Lattice.ior_interiorSubset_iff_leftRegion_subset K a

/--
[ior_leftRegion_bdEdge_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_leftRegion_bdEdge_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v)) :
-- imply
  u ∈ (mpl_orbitLoop K a).support ∨ v ∈ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Lattice.ior_leftRegion_bdEdge_support K a hadj hbd

/--
[ior_orbit_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_orbit_tail_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {i : ℕ} :
-- imply
  ((dartNext K)^[i] a.1).tail ∈ K := by
-- proof
  apply StatMech.Lattice.ior_orbit_tail_mem K a i

/--
[ior_windingWitness_of_tail_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_windingWitness_of_tail_odd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (htail : ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (mpl_orbitLoop K a))) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.ior_windingWitness_of_tail_odd K a htail

/--
[ior_windingWitness_of_cycle_tail_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InteriorOrientation.lean)
-/
@[path]
private lemma ior_windingWitness_of_cycle_tail_odd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (htail : ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (mpl_orbitLoop K a))) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.ior_windingWitness_of_cycle_tail_odd K a htail


-- created on 2026-10-23
