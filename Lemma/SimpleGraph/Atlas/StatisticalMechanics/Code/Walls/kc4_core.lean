import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc4_core.Part2
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc4_reaches_exterior_of_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_reaches_exterior_of_infiniteComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hzmem : z ∈ (oc_supportSet Vc)ᶜ)
  (hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Walls.kc4_reaches_exterior_of_infiniteComponent Vc R hsupp hzmem hinf

/--
[kc4_extComponent_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_extComponent_infinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {e : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (heExt : e ∈ exterior 2 R)
  (hemem : e ∈ (oc_supportSet Vc)ᶜ) :
-- imply
  (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨e, hemem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc4_extComponent_infinite Vc R hsupp heExt hemem

/--
[kc4_outsideReachesExterior_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_outsideReachesExterior_of_infinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hres : kc4_OutsideInInfiniteComponent Vc) :
-- imply
  oc_OutsideReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc4_outsideReachesExterior_of_infinite Vc R hsupp hres

/--
[kc4_infinite_of_outsideReachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_infinite_of_outsideReachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hflood : oc_OutsideReachesExterior Vc R) :
-- imply
  kc4_OutsideInInfiniteComponent Vc := by
-- proof
  apply StatMech.Walls.kc4_infinite_of_outsideReachesExterior Vc R hsupp hflood

/--
[kc4_outsideReachesExterior_iff_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_outsideReachesExterior_iff_infinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R) :
-- imply
  oc_OutsideReachesExterior Vc R ↔ kc4_OutsideInInfiniteComponent Vc := by
-- proof
  apply StatMech.Walls.kc4_outsideReachesExterior_iff_infinite Vc R hsupp

/--
[kc4_orbit_outsideReachesExterior_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_orbit_outsideReachesExterior_of_infinite_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hres : kc4_OutsideInInfiniteComponent (mpl_orbitLoop K a)) :
-- imply
  oc_OutsideReachesExterior (mpl_orbitLoop K a) R := by
-- proof
  apply StatMech.Walls.kc4_orbit_outsideReachesExterior_of_infinite K a R hRbox hres

/--
[kc4_exc_offSupportReaches_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_exc_offSupportReaches_of_infinite_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hint : eaw_InteriorSubset K a)
  (hres : kc4_OutsideInInfiniteComponent (mpl_orbitLoop K a)) :
-- imply
  exc_OffSupportReachesExterior K a := by
-- proof
  apply StatMech.Walls.kc4_exc_offSupportReaches_of_infinite K a R hRbox hint hres

/--
[kc4_exterior_in_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_exterior_in_infiniteComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ, (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc4_exterior_in_infiniteComponent Vc R hsupp hz

/--
[kc4_residue_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_residue_nonvacuous_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ jec_leftRegion Vc ∧ ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ, (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩).supp.Infinite := by
-- proof
  apply StatMech.Walls.kc4_residue_nonvacuous Vc R hsupp hz

/--
[kc4_orbitLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_orbitLoop_isCycle_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  (mpl_orbitLoop K a).IsCycle := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_isCycle K a hp hinj

/--
[kc4_contour_eulerOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean)
-/
@[path]
private lemma kc4_contour_eulerOne_eq
  {a : Site 2}
  {p : ℕ}
-- given
  (hp : 3 ≤ p) :
-- imply
  kc4_contourEulerChar p = 1 := by
-- proof
  apply StatMech.Walls.kc4_contour_eulerOne hp


-- created on 2026-10-23
