import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[offSupport_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_adj_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2} :
-- imply
  (offSupport Vc).Adj x y ↔ (hypercubicLattice 2).Adj x y ∧ x ∉ Vc.support ∧ y ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.offSupport_adj Vc x y

/--
[offSupport_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_le_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  offSupport Vc ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.offSupport_le Vc

/--
[offSupport_walk_support_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_walk_support_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (offSupport Vc).Walk x y}
-- given
  (hx : x ∉ Vc.support) :
-- imply
  ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.offSupport_walk_support_offSupport Vc p hx

/--
[offSupport_to_offSupportWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_to_offSupportWalk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (offSupport Vc).Walk x y}
-- given
  (hx : x ∉ Vc.support) :
-- imply
  ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.offSupport_to_offSupportWalk Vc p hx

/--
[offSupport_reachable_to_offSupportWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_reachable_to_offSupportWalk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (h : (offSupport Vc).Reachable x y)
  (hx : x ∉ Vc.support) :
-- imply
  ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.offSupport_reachable_to_offSupportWalk Vc h hx

/--
[offSupportWalk_to_offSupport_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupportWalk_to_offSupport_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable x y := by
-- proof
  apply StatMech.Lattice.offSupportWalk_to_offSupport_reachable Vc p hp

/--
[offSupport_reachable_iff_offSupportWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_reachable_iff_offSupportWalk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable x y ↔ ∃ pw : (hypercubicLattice 2).Walk x y, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.offSupport_reachable_iff_offSupportWalk Vc hx

/--
[inside_sameRegion_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma inside_sameRegion_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (h : (offSupport Vc).Reachable x y)
  (hx : x ∉ Vc.support) :
-- imply
  (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.inside_sameRegion_offSupport Vc h hx

/--
[offSupport_component_monochromatic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_component_monochromatic_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s t : Site 2}
-- given
  (hs : s ∈ jec_leftRegion Vc)
  (hst : (offSupport Vc).Reachable s t)
  (hsoff : s ∉ Vc.support) :
-- imply
  t ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.offSupport_component_monochromatic Vc hs hst hsoff

/--
[offSupport_component_monochromatic_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_component_monochromatic_out_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s t : Site 2}
-- given
  (hs : s ∉ jec_leftRegion Vc)
  (hst : (offSupport Vc).Reachable s t)
  (hsoff : s ∉ Vc.support) :
-- imply
  t ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.offSupport_component_monochromatic_out Vc hs hst hsoff

/--
[hInOff_of_offSupport_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma hInOff_of_offSupport_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hconn : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (offSupport Vc).Reachable s t) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.hInOff_of_offSupport_connected Vc hoff hconn

/--
[inside_offSupport_connected_of_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma inside_offSupport_connected_of_hub_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c₀ : Site 2}
-- given
  (hhub : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (offSupport Vc).Reachable s t := by
-- proof
  apply StatMech.Lattice.inside_offSupport_connected_of_hub Vc hhub

/--
[hInOff_of_interiorHub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma hInOff_of_interiorHub_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c₀ : Site 2}
-- given
  (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hhub : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.hInOff_of_interiorHub Vc hoff hhub

/--
[hOutOff_of_exteriorHub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma hOutOff_of_exteriorHub_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {d₀ : Site 2}
-- given
  (hoff : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
  (hhub : ∀ s : Site 2, s ∉ jec_leftRegion Vc → (offSupport Vc).Reachable d₀ s) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.hOutOff_of_exteriorHub Vc hoff hhub

/--
[two_components_of_hubs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma two_components_of_hubs_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
  {c₀ d₀ : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
  (hubIn : ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable c₀ s)
  (hubOut : ∀ s : Site 2, s ∉ jec_leftRegion Vc → (offSupport Vc).Reachable d₀ s) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.two_components_of_hubs Vc hp hq hoffIn hoffOut hubIn hubOut

/--
[minimalLoop_inside_sameRegion_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma minimalLoop_inside_sameRegion_offSupport_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {x y : Site 2}
-- given
  (h : (offSupport (mpl_orbitLoop K a)).Reachable x y)
  (hx : x ∉ (mpl_orbitLoop K a).support) :
-- imply
  (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Lattice.minimalLoop_inside_sameRegion_offSupport K a h hx

/--
[minimalLoop_hInOff_of_interiorHub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma minimalLoop_hInOff_of_interiorHub_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c₀ : Site 2}
-- given
  (hoff : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hhub : ∀ s : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) → (offSupport (mpl_orbitLoop K a)).Reachable c₀ s) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) → t ∈ jec_leftRegion (mpl_orbitLoop K a) → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Lattice.minimalLoop_hInOff_of_interiorHub K a hoff hhub

/--
[minimalLoop_two_components_of_hubs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma minimalLoop_two_components_of_hubs_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {p q : Site 2}
  {c₀ d₀ : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
  (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
  (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hoffOut : ∀ s ∉ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hubIn : ∀ s : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) → (offSupport (mpl_orbitLoop K a)).Reachable c₀ s)
  (hubOut : ∀ s : Site 2, s ∉ jec_leftRegion (mpl_orbitLoop K a) → (offSupport (mpl_orbitLoop K a)).Reachable d₀ s) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.minimalLoop_two_components_of_hubs K a hp hq hoffIn hoffOut hubIn hubOut

/--
[mem_offSupportComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma mem_offSupportComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed z : Site 2} :
-- imply
  z ∈ offSupportComponent Vc seed ↔ (offSupport Vc).Reachable seed z := by
-- proof
  apply StatMech.Lattice.mem_offSupportComponent Vc

/--
[seed_mem_offSupportComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma seed_mem_offSupportComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2} :
-- imply
  seed ∈ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.seed_mem_offSupportComponent Vc seed

/--
[offSupportComponent_subset_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupportComponent_subset_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∈ jec_leftRegion Vc)
  (hsoff : seed ∉ Vc.support) :
-- imply
  offSupportComponent Vc seed ⊆ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.offSupportComponent_subset_interior Vc hseed hsoff

/--
[offSupportComponent_subset_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupportComponent_subset_exterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ jec_leftRegion Vc)
  (hsoff : seed ∉ Vc.support) :
-- imply
  offSupportComponent Vc seed ⊆ (jec_leftRegion Vc)ᶜ := by
-- proof
  apply StatMech.Lattice.offSupportComponent_subset_exterior Vc hseed hsoff

/--
[offSupportComponent_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupportComponent_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {z : Site 2}
-- given
  (hsoff : seed ∉ Vc.support)
  (hz : z ∈ offSupportComponent Vc seed) :
-- imply
  z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.offSupportComponent_offSupport Vc hsoff hz

/--
[offSupportComponent_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupportComponent_hub_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2} :
-- imply
  ∀ z : Site 2, z ∈ offSupportComponent Vc seed → (offSupport Vc).Reachable seed z := by
-- proof
  apply StatMech.Lattice.offSupportComponent_hub Vc seed

/--
[interior_eq_offSupportComponent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma interior_eq_offSupportComponent_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∈ jec_leftRegion Vc)
  (hsoff : seed ∉ Vc.support) :
-- imply
  jec_leftRegion Vc = offSupportComponent Vc seed ↔ jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.interior_eq_offSupportComponent_iff Vc hseed hsoff

/--
[interiorHub_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma interiorHub_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
-- imply
  ∀ s : Site 2, s ∈ jec_leftRegion Vc → (offSupport Vc).Reachable seed s := by
-- proof
  apply StatMech.Lattice.interiorHub_of_covers Vc hcov

/--
[hInOff_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma hInOff_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.hInOff_of_covers Vc hoff hcov

/--
[inside_offSupport_connected_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma inside_offSupport_connected_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc seed) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (offSupport Vc).Reachable s t := by
-- proof
  apply StatMech.Lattice.inside_offSupport_connected_of_covers Vc hcov

/--
[cycle_boundedRegionCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma cycle_boundedRegionCount_one_eq
  {G : SimpleGraph V}
  [Empty.Finite V]
  [DecidableEq V]
  {w : V}
  {c : G.Walk w w}
-- given
  (hc : c.IsCycle) :
-- imply
  jes_boundedRegionCount c.toSubgraph.coe = 1 := by
-- proof
  apply StatMech.Lattice.cycle_boundedRegionCount_one c hc

/--
[two_components_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma two_components_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
  {sIn sOut : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
  (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
  (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.two_components_of_covers Vc hp hq hoffIn hoffOut hcovIn hcovOut

/--
[minimalLoop_offSupportComponent_subset_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma minimalLoop_offSupportComponent_subset_interior_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {seed : Site 2}
-- given
  (hseed : seed ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hsoff : seed ∉ (mpl_orbitLoop K a).support) :
-- imply
  offSupportComponent (mpl_orbitLoop K a) seed ⊆ jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Lattice.minimalLoop_offSupportComponent_subset_interior K a hseed hsoff

/--
[minimalLoop_hInOff_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma minimalLoop_hInOff_of_covers_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {seed : Site 2}
-- given
  (hoff : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hcov : jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) seed) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) → t ∈ jec_leftRegion (mpl_orbitLoop K a) → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Lattice.minimalLoop_hInOff_of_covers K a hoff hcov

/--
[minimalLoop_two_components_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma minimalLoop_two_components_of_covers_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {p q : Site 2}
  {sIn sOut : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
  (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
  (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hoffOut : ∀ s ∉ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hcovIn : jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) sIn)
  (hcovOut : (jec_leftRegion (mpl_orbitLoop K a))ᶜ ⊆ offSupportComponent (mpl_orbitLoop K a) sOut) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.minimalLoop_two_components_of_covers K a hp hq hoffIn hoffOut hcovIn hcovOut

/--
[offSupport_reachable_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_reachable_symm_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (h : (offSupport Vc).Reachable x y) :
-- imply
  (offSupport Vc).Reachable y x := by
-- proof
  apply StatMech.Lattice.offSupport_reachable_symm Vc h

/--
[offSupport_reachable_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma offSupport_reachable_trans_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y z : Site 2}
-- given
  (hxy : (offSupport Vc).Reachable x y)
  (hyz : (offSupport Vc).Reachable y z) :
-- imply
  (offSupport Vc).Reachable x z := by
-- proof
  apply StatMech.Lattice.offSupport_reachable_trans Vc hxy hyz

/--
[inside_offSupport_connected_iff_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma inside_offSupport_connected_iff_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∈ jec_leftRegion Vc) :
-- imply
  (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (offSupport Vc).Reachable s t) ↔ jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.inside_offSupport_connected_iff_covers Vc hseed

/--
[hInOff_iff_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideConnected.lean)
-/
@[path]
private lemma hInOff_iff_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hseed : seed ∈ jec_leftRegion Vc) :
-- imply
  (∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support) ↔ jec_leftRegion Vc ⊆ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.hInOff_iff_covers Vc hoff hseed


-- created on 2026-10-23
