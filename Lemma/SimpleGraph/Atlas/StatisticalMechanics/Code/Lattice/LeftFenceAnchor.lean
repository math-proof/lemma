import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.LeftFenceAnchor
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[lfa_leftFence_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_leftFence_anchor_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ z₀ ∈ K, IsBoundaryDart K (lmo_leftDartAt z₀) ∧ (∀ w ∈ K, z₀ 0 ≤ w 0) := by
-- proof
  apply StatMech.Lattice.lfa_leftFence_anchor K hK hne

/--
[lfa_leftFence_on_own_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_leftFence_on_own_orbit_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
-- given
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) :
-- imply
  ∃ n : ℕ, (dartNext K)^[n] (⟨lmo_leftDartAt z₀, hbd⟩ : {e : Dart // IsBoundaryDart K e}).1 = lmo_leftDartAt z₀ := by
-- proof
  apply StatMech.Lattice.lfa_leftFence_on_own_orbit K z₀ hbd

/--
[lfa_leftFence_reachesLeftmost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_leftFence_reachesLeftmost_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
  (hm : z₀ 0 = m) :
-- imply
  lmo_OrbitReachesLeftmost K ⟨lmo_leftDartAt z₀, hbd⟩ m := by
-- proof
  apply StatMech.Lattice.lfa_leftFence_reachesLeftmost K hK z₀ hbd m hm

/--
[lfa_leftFence_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_leftFence_windingWitness_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
  (hm : z₀ 0 = m)
  (hmin : ∀ w ∈ K, m ≤ w 0)
  (hcyc : (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle) :
-- imply
  wei_WindingWitness K ⟨lmo_leftDartAt z₀, hbd⟩ := by
-- proof
  apply StatMech.Lattice.lfa_leftFence_windingWitness K hK z₀ hbd m hm hmin hcyc

/--
[lfa_exists_anchor_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_exists_anchor_windingWitness_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hcyc : ∀ z₀ : Site 2, ∀ hbd : IsBoundaryDart K (lmo_leftDartAt z₀), (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle) :
-- imply
  ∃ a : {e : Dart // IsBoundaryDart K e}, wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.lfa_exists_anchor_windingWitness K hK hne hcyc

/--
[lfa_starHull_leftFence_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_starHull_leftFence_windingWitness_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀))
  (hm : z₀ 0 = m)
  (hmin : ∀ w ∈ ndt_StarHull K, m ≤ w 0)
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) :
-- imply
  wei_WindingWitness (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩ := by
-- proof
  apply StatMech.Lattice.lfa_starHull_leftFence_windingWitness K hK z₀ hbd m hm hmin hp

/--
[lfa_starHull_exists_anchor_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_starHull_exists_anchor_windingWitness_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hp : ∀ z₀ : Site 2, ∀ hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀), 3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) :
-- imply
  ∃ a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}, wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.lfa_starHull_exists_anchor_windingWitness K hK hne hp

/--
[lfa_windingWitness_of_interiorSubset_and_enclosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_windingWitness_of_interiorSubset_and_enclosed_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hint : eaw_InteriorSubset K a)
  (henc : ∃ z : Site 2, ¬ Even (jec_rayCount z (mpl_orbitLoop K a))) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.lfa_windingWitness_of_interiorSubset_and_enclosed K a hint henc

/--
[lfa_consumer_needs_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_consumer_needs_interiorSubset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hnp : OrbitFaceNoPinch K a)
  (hint : eaw_InteriorSubset K a) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.lfa_consumer_needs_interiorSubset K a hp hnp hint

/--
[lfa_distinct_dart_same_orbit_not_reflexive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_distinct_dart_same_orbit_not_reflexive_eq
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (hne : e ≠ f) :
-- imply
  ¬ ((dartNext K)^[0] e = f) := by
-- proof
  apply StatMech.Lattice.lfa_distinct_dart_same_orbit_not_reflexive K hne

/--
[lfa_foreign_anchor_needs_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_foreign_anchor_needs_interfaceConnected_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z₀ : Site 2}
-- given
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
  (hInt : InterfaceConnected K)
  (hcomp : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩) :
-- imply
  ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀ := by
-- proof
  apply StatMech.Lattice.lfa_foreign_anchor_needs_interfaceConnected K a z₀ hbd hInt hcomp

/--
[lfa_unitCell_leftFence_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_unitCell_leftFence_isBoundaryDart_eq :
-- imply
  IsBoundaryDart unitCell (lmo_leftDartAt (![0, 0] : Site 2)) := by
-- proof
  apply StatMech.Lattice.lfa_unitCell_leftFence_isBoundaryDart

/--
[lfa_unitCell_leftFence_reachesLeftmost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFenceAnchor.lean)
-/
@[path]
private lemma lfa_unitCell_leftFence_reachesLeftmost_eq :
-- imply
  lmo_OrbitReachesLeftmost unitCell ⟨lmo_leftDartAt (![0, 0] : Site 2), lfa_unitCell_leftFence_isBoundaryDart⟩ 0 := by
-- proof
  apply StatMech.Lattice.lfa_unitCell_leftFence_reachesLeftmost


-- created on 2026-10-23
