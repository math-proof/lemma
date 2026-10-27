import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnectedDischarge
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ecd_wwcExt_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_wwcExt_false_eq :
-- imply
  ¬ (∀ z, z ∉ unitCell → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∧ (∀ q ∈ (mpl_orbitLoop unitCell ucBase).support, z0 0 ≤ q 0)) := by
-- proof
  apply StatMech.Lattice.ecd_wwcExt_false

/--
[ecd_exterior_reaches_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_exterior_reaches_farLeft_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) := by
-- proof
  apply StatMech.Lattice.ecd_exterior_reaches_farLeft K a R hR z hz

/--
[ecd_interiorSubset_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_interiorSubset_of_exc_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Lattice.ecd_interiorSubset_of_exc K a hoff hsupp

/--
[ecd_leftRegion_subset_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_leftRegion_subset_of_exc_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
-- proof
  apply StatMech.Lattice.ecd_leftRegion_subset_of_exc K a hoff hsupp

/--
[ecd_windingWitness_of_cycle_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_windingWitness_of_cycle_exc_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hnp : OrbitFaceNoPinch K a)
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.ecd_windingWitness_of_cycle_exc K a hp hnp hoff hsupp

/--
[ecd_loopWindsRegion_conjuncts_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_loopWindsRegion_conjuncts_of_exc_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hnp : OrbitFaceNoPinch K a)
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a ∧ eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Lattice.ecd_loopWindsRegion_conjuncts_of_exc K a hp hnp hoff hsupp

/--
[ecd_loopWindsRegion_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_loopWindsRegion_of_exc_eq
-- given
  (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → 3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
  (hoff : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → exc_OffSupportReachesExterior K a)
  (hsupp : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → exc_SupportOddInK K a) :
-- imply
  eaw_LoopWindsRegion := by
-- proof
  apply StatMech.Lattice.ecd_loopWindsRegion_of_exc hcyc hoff hsupp

/--
[ecd_windingSaturatingWitness_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_windingSaturatingWitness_of_exc_eq
-- given
  (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → 3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
  (hoff : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → exc_OffSupportReachesExterior K a)
  (hsupp : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → exc_SupportOddInK K a) :
-- imply
  wei_WindingSaturatingWitness := by
-- proof
  apply StatMech.Lattice.ecd_windingSaturatingWitness_of_exc hcyc hoff hsupp

/--
[ecd_starHull_windingWitness_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_starHull_windingWitness_of_exc_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hcyc : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → 3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a)
  (hoff : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → exc_OffSupportReachesExterior K a)
  (hsupp : ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard → ∀ (a : {e : Dart // IsBoundaryDart K e}), K ⊆ bpc_orbitFootprint K a → exc_SupportOddInK K a)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.ecd_starHull_windingWitness_of_exc hcyc hoff hsupp K hSK hne a

/--
[ecd_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ExteriorConnectedDischarge.lean)
-/
@[path]
private lemma ecd_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.ecd_unitCell_windingWitness


-- created on 2026-10-23
