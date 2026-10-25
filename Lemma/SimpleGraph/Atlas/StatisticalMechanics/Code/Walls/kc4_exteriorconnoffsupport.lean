import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc4_exteriorconnoffsupport
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc4_exterior_reachable_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_exterior_reachable_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
-- proof
  apply StatMech.Walls.kc4_exterior_reachable_offSupport Vc R hsupp hx hy

/--
[kc4_exterior_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_exterior_offSupport_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_exterior_offSupport_walk Vc R hsupp hx hy

/--
[kc4_exterior_mem_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_exterior_mem_compl_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∈ (oc_supportSet Vc)ᶜ := by
-- proof
  apply StatMech.Walls.kc4_exterior_mem_compl Vc R hsupp hz

/--
[kc4_exterior_reachable_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_exterior_reachable_induce_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable ⟨x, kc4_exterior_mem_compl Vc R hsupp hx⟩ ⟨y, kc4_exterior_mem_compl Vc R hsupp hy⟩ := by
-- proof
  apply StatMech.Walls.kc4_exterior_reachable_induce Vc R hsupp hx hy

/--
[kc4_orbit_exterior_reachable_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_orbit_exterior_reachable_induce_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  ((hypercubicLattice 2).induce ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable ⟨x, exterior_subset_compl _ R hRbox hx⟩ ⟨y, exterior_subset_compl _ R hRbox hy⟩ := by
-- proof
  apply StatMech.Walls.kc4_orbit_exterior_reachable_induce K a R hRbox hx hy

/--
[kc4_orbit_exterior_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_orbit_exterior_offSupport_walk_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Walls.kc4_orbit_exterior_offSupport_walk K a R hRbox hx hy

/--
[kc4_orbit_loopSupportBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_orbit_loopSupportBox_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ∃ R : ℕ, ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R := by
-- proof
  apply StatMech.Walls.kc4_orbit_loopSupportBox K a

/--
[kc4_orbit_exterior_reachable_induce_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exteriorconnoffsupport.lean)
-/
@[path]
private lemma kc4_orbit_exterior_reachable_induce_exists_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ∃ R : ℕ, ∃ hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R, ∀ x y : Site 2, ∀ (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R), ((hypercubicLattice 2).induce ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2))ᶜ).Reachable ⟨x, exterior_subset_compl _ R hRbox hx⟩ ⟨y, exterior_subset_compl _ R hRbox hy⟩ := by
-- proof
  apply StatMech.Walls.kc4_orbit_exterior_reachable_induce_exists K a


-- created on 2026-10-23
