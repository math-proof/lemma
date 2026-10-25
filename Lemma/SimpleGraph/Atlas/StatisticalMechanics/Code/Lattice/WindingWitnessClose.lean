import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitnessClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wwc_outside_even_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_outside_even_of_exterior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Lattice.wwc_outside_even_of_exterior K a hExt

/--
[wwc_leftRegion_subset_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_leftRegion_subset_of_exterior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
-- proof
  apply StatMech.Lattice.wwc_leftRegion_subset_of_exterior K a hExt

/--
[wwc_interiorSubset_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_interiorSubset_of_exterior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Lattice.wwc_interiorSubset_of_exterior K a hExt

/--
[wwc_windingWitness_of_cycle_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_windingWitness_of_cycle_exterior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)))
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.wwc_windingWitness_of_cycle_exterior K a hp hinj hExt

/--
[wwc_windingWitness_of_noPinch_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_windingWitness_of_noPinch_exterior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hnp : OrbitFaceNoPinch K a)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.wwc_windingWitness_of_noPinch_exterior K a hp hnp hExt

/--
[wwc_loopWindsRegion_conjuncts_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_loopWindsRegion_conjuncts_of_exterior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hnp : OrbitFaceNoPinch K a)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a ∧ eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Lattice.wwc_loopWindsRegion_conjuncts_of_exterior K a hp hnp hExt

/--
[wwc_loopWindsRegion_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_loopWindsRegion_of_exterior_eq
-- given
  (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → 3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
  (hExt : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  eaw_LoopWindsRegion := by
-- proof
  apply StatMech.Lattice.wwc_loopWindsRegion_of_exterior hcyc hExt

/--
[wwc_windingSaturatingWitness_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_windingSaturatingWitness_of_exterior_eq
-- given
  (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → 3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
  (hExt : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  wei_WindingSaturatingWitness := by
-- proof
  apply StatMech.Lattice.wwc_windingSaturatingWitness_of_exterior hcyc hExt

/--
[wwc_starHull_windingWitness_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_starHull_windingWitness_of_exterior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → 3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
  (hExt : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0))
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.wwc_starHull_windingWitness_of_exterior hcyc hExt K hSK hne a

/--
[wwc_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose.lean)
-/
@[path]
private lemma wwc_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.wwc_unitCell_windingWitness


-- created on 2026-10-23
