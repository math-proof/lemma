import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.OrbitCoversBoundary
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ocb_leftFence_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_leftFence_data_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ z₀ ∈ K, IsBoundaryDart K (lmo_leftDartAt z₀) ∧ (lmo_leftDartAt z₀).dir = ![-1, 0] ∧ (lmo_leftDartAt z₀).tail 0 = z₀ 0 ∧ (∀ w ∈ K, z₀ 0 ≤ w 0) := by
-- proof
  apply StatMech.Lattice.ocb_leftFence_data K hK hne

/--
[ocb_on_orbit_index_lt_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_on_orbit_index_lt_period_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (hn : (dartNext K)^[n] a.1 = e) :
-- imply
  ∃ k < dartOrbitPeriod K a, (dartNext K)^[k] a.1 = e := by
-- proof
  apply StatMech.Lattice.ocb_on_orbit_index_lt_period K hK a hn

/--
[ocb_reachesLeftmost_of_leftFence_on_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_reachesLeftmost_of_leftFence_on_orbit_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hm : z₀ 0 = m)
  (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀) :
-- imply
  lmo_OrbitReachesLeftmost K a m := by
-- proof
  apply StatMech.Lattice.ocb_reachesLeftmost_of_leftFence_on_orbit K hK a z₀ m hm hon

/--
[ocb_windingWitness_of_leftFence_on_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_windingWitness_of_leftFence_on_orbit_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hm : z₀ 0 = m)
  (hmin : ∀ w ∈ K, m ≤ w 0)
  (hcyc : (mpl_orbitLoop K a).IsCycle)
  (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.ocb_windingWitness_of_leftFence_on_orbit K hK a z₀ m hm hmin hcyc hon

/--
[ocb_leftFence_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_leftFence_head_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
-- given
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) :
-- imply
  (lmo_leftDartAt z₀).head ∉ K := by
-- proof
  apply StatMech.Lattice.ocb_leftFence_head hbd

/--
[ocb_leftFence_head_sameComponent_of_on_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_leftFence_head_sameComponent_of_on_orbit_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z₀ : Site 2}
-- given
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
  (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩ := by
-- proof
  apply StatMech.Lattice.ocb_leftFence_head_sameComponent_of_on_orbit a hbd hon

/--
[ocb_leftFence_on_orbit_of_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_leftFence_on_orbit_of_sameComponent_eq
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
  apply StatMech.Lattice.ocb_leftFence_on_orbit_of_sameComponent a hbd hInt hcomp

/--
[ocb_leftFence_on_orbit_iff_headSameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_leftFence_on_orbit_iff_headSameComponent_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z₀ : Site 2}
-- given
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
  (hInt : InterfaceConnected K) :
-- imply
  (∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀) ↔ ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩ := by
-- proof
  apply StatMech.Lattice.ocb_leftFence_on_orbit_iff_headSameComponent a hbd hInt

/--
[ocb_starHull_windingWitness_of_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_starHull_windingWitness_of_interfaceConnected_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
  (hInt : InterfaceConnected (ndt_StarHull K)) :
-- imply
  (∀ (z₀ : Site 2) (hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀)), z₀ ∈ ndt_StarHull K → (∀ w ∈ ndt_StarHull K, z₀ 0 ≤ w 0) → ((hypercubicLattice 2).induce (ndt_StarHull K)ᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩) → wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.ocb_starHull_windingWitness_of_interfaceConnected K hK hne a hp hInt

/--
[ocb_unitCell_reachesLeftmost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_unitCell_reachesLeftmost_eq :
-- imply
  lmo_OrbitReachesLeftmost unitCell ucBase 0 := by
-- proof
  apply StatMech.Lattice.ocb_unitCell_reachesLeftmost

/--
[ocb_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitCoversBoundary.lean)
-/
@[path]
private lemma ocb_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.ocb_unitCell_windingWitness


-- created on 2026-10-23
