import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.InsideCoveringClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[icc_offComplGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_offComplGraph_adj_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (x y : {z : Site 2 // z ∉ Vc.support}) :
-- imply
  (icc_offComplGraph Vc).Adj x y ↔ (offSupport Vc).Adj (x : Site 2) (y : Site 2) := by
-- proof
  apply StatMech.Lattice.icc_offComplGraph_adj Vc x y

/--
[icc_induce_reachable_to_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_induce_reachable_to_ambient_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}}
-- given
  (h : (icc_offComplGraph Vc).Reachable x y) :
-- imply
  (offSupport Vc).Reachable (x : Site 2) (y : Site 2) := by
-- proof
  apply StatMech.Lattice.icc_induce_reachable_to_ambient Vc h

/--
[icc_ambient_reachable_to_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_ambient_reachable_to_induce_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}}
-- given
  (h : (offSupport Vc).Reachable (x : Site 2) (y : Site 2)) :
-- imply
  (icc_offComplGraph Vc).Reachable x y := by
-- proof
  apply StatMech.Lattice.icc_ambient_reachable_to_induce Vc h

/--
[icc_induce_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_induce_reachable_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}} :
-- imply
  (icc_offComplGraph Vc).Reachable x y ↔ (offSupport Vc).Reachable (x : Site 2) (y : Site 2) := by
-- proof
  apply StatMech.Lattice.icc_induce_reachable_iff Vc

/--
[icc_mem_offSupportComponent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_mem_offSupportComponent_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}} :
-- imply
  (icc_offComplGraph Vc).connectedComponentMk x = (icc_offComplGraph Vc).connectedComponentMk y ↔ (y : Site 2) ∈ offSupportComponent Vc (x : Site 2) := by
-- proof
  apply StatMech.Lattice.icc_mem_offSupportComponent_iff Vc

/--
[icc_card_two_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_card_two_dichotomy_eq
  {a : Site 2}
  {a b : α}
  {c : α}
-- given
  (h : Nat.card α = 2)
  (hab : a ≠ b) :
-- imply
  c = a ∨ c = b := by
-- proof
  apply StatMech.Lattice.icc_card_two_dichotomy h hab c

/--
[icc_card_two_dichotomy_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_card_two_dichotomy_nonvacuous_eq
  {a : Site 2}
  {c : Bool} :
-- imply
  c = true ∨ c = false := by
-- proof
  apply StatMech.Lattice.icc_card_two_dichotomy_nonvacuous c

/--
[icc_components_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_components_distinct_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : {z : Site 2 // z ∉ Vc.support}}
-- given
  (hInMem : (sIn : Site 2) ∈ jec_leftRegion Vc)
  (hOutMem : (sOut : Site 2) ∉ jec_leftRegion Vc) :
-- imply
  (icc_offComplGraph Vc).connectedComponentMk sIn ≠ (icc_offComplGraph Vc).connectedComponentMk sOut := by
-- proof
  apply StatMech.Lattice.icc_components_distinct Vc hInMem hOutMem

/--
[icc_covers_of_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_covers_of_two_components_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : Site 2}
-- given
  (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hInOff : sIn ∉ Vc.support)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hOutOff : sOut ∉ Vc.support)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
-- imply
  jec_leftRegion Vc ⊆ offSupportComponent Vc sIn := by
-- proof
  apply StatMech.Lattice.icc_covers_of_two_components Vc hcard hInMem hInOff hOutMem hOutOff hoffIn

/--
[icc_interior_eq_offSupportComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_interior_eq_offSupportComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : Site 2}
-- given
  (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hInOff : sIn ∉ Vc.support)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hOutOff : sOut ∉ Vc.support)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
-- imply
  jec_leftRegion Vc = offSupportComponent Vc sIn := by
-- proof
  apply StatMech.Lattice.icc_interior_eq_offSupportComponent Vc hcard hInMem hInOff hOutMem hOutOff hoffIn

/--
[icc_inside_offSupport_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_inside_offSupport_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : Site 2}
-- given
  (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hInOff : sIn ∉ Vc.support)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hOutOff : sOut ∉ Vc.support)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (offSupport Vc).Reachable s t := by
-- proof
  apply StatMech.Lattice.icc_inside_offSupport_connected Vc hcard hInMem hInOff hOutMem hOutOff hoffIn

/--
[icc_hInOff_of_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_hInOff_of_two_components_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : Site 2}
-- given
  (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hInOff : sIn ∉ Vc.support)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hOutOff : sOut ∉ Vc.support)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.icc_hInOff_of_two_components Vc hcard hInMem hInOff hOutMem hOutOff hoffIn

/--
[icc_two_components_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_two_components_of_count_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
  {sIn sOut : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hcard : Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hInOff : sIn ∉ Vc.support)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hOutOff : sOut ∉ Vc.support)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hOut : oc_OutsideReachesExterior Vc R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.icc_two_components_of_count Vc R hsupp hp hq hcard hInMem hInOff hOutMem hOutOff hoffIn hOut

/--
[icc_minimalLoop_covers_of_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_minimalLoop_covers_of_two_components_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {sIn sOut : Site 2}
-- given
  (hcard : Nat.card (icc_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
  (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
  (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
  (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support) :
-- imply
  jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) sIn := by
-- proof
  apply StatMech.Lattice.icc_minimalLoop_covers_of_two_components K a hcard hInMem hInOff hOutMem hOutOff hoffIn

/--
[icc_minimalLoop_hInOff_of_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_minimalLoop_hInOff_of_two_components_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {sIn sOut : Site 2}
-- given
  (hcard : Nat.card (icc_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
  (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
  (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
  (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) → t ∈ jec_leftRegion (mpl_orbitLoop K a) → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support := by
-- proof
  apply StatMech.Lattice.icc_minimalLoop_hInOff_of_two_components K a hcard hInMem hInOff hOutMem hOutOff hoffIn

/--
[icc_minimalLoop_two_components_of_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InsideCoveringClose.lean)
-/
@[path]
private lemma icc_minimalLoop_two_components_of_count_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {p q : Site 2}
  {sIn sOut : Site 2}
-- given
  (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
  (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
  (hcard : Nat.card (icc_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2)
  (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
  (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
  (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
  (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hOut : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.icc_minimalLoop_two_components_of_count K a R hsupp hp hq hcard hInMem hInOff hOutMem hOutOff hoffIn hOut


-- created on 2026-10-23
