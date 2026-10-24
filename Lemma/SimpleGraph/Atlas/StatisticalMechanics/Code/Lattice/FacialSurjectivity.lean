import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.FacialSurjectivity
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[fsv_range_eq_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_range_eq_canonical_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Set.range (rsf_componentDarts Vc) = fsv_canonicalFamily Vc := by
-- proof
  apply StatMech.Lattice.fsv_range_eq_canonical Vc

/--
[fsv_facialOrbitsCoverComponents_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_facialOrbitsCoverComponents_canonical_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  rsf_FacialOrbitsCoverComponents Vc (fsv_canonicalFamily Vc) := by
-- proof
  apply StatMech.Lattice.fsv_facialOrbitsCoverComponents_canonical Vc

/--
[fsv_componentCount_eq_canonicalCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_componentCount_eq_canonicalCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = Nat.card (fsv_canonicalFamily Vc) := by
-- proof
  apply StatMech.Lattice.fsv_componentCount_eq_canonicalCount Vc

/--
[fsv_boundaryDartSet_dartNext_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_boundaryDartSet_dartNext_closed_eq
  {C : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart C e) :
-- imply
  IsBoundaryDart C (dartNext C e) := by
-- proof
  apply StatMech.Lattice.fsv_boundaryDartSet_dartNext_closed C he

/--
[fsv_orbit_subset_boundaryDartSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_orbit_subset_boundaryDartSet_eq
  {C : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart C e) :
-- imply
  {d : Dart | SameOrbit C e d} ⊆ {d : Dart | IsBoundaryDart C d} := by
-- proof
  apply StatMech.Lattice.fsv_orbit_subset_boundaryDartSet C he

/--
[fsv_canonicalFamily_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_canonicalFamily_nonempty_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {D : Set Dart}
-- given
  (hD : D ∈ fsv_canonicalFamily Vc) :
-- imply
  D.Nonempty := by
-- proof
  apply StatMech.Lattice.fsv_canonicalFamily_nonempty Vc hD

/--
[fsv_boundaryDartSet_eq_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_boundaryDartSet_eq_orbit_eq
  {C : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart C e)
  (hsat : ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d) :
-- imply
  {d : Dart | IsBoundaryDart C d} = {d : Dart | SameOrbit C e d} := by
-- proof
  apply StatMech.Lattice.fsv_boundaryDartSet_eq_orbit C he hsat

/--
[fsv_hsat_of_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_hsat_of_interfaceConnected_eq
  {C : Set (Site 2)}
  {e : Dart}
-- given
  (hIC : InterfaceConnected C)
  (he : IsBoundaryDart C e)
  (hheads : ∀ d : Dart, (hd : IsBoundaryDart C d) → ((hypercubicLattice 2).induce Cᶜ).Reachable ⟨e.head, he.2⟩ ⟨d.head, hd.2⟩) :
-- imply
  ∀ d : Dart, IsBoundaryDart C d → SameOrbit C e d := by
-- proof
  apply StatMech.Lattice.fsv_hsat_of_interfaceConnected C hIC he hheads

/--
[fsv_canonicalMember_eq_orbit_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_canonicalMember_eq_orbit_of_residues_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {e : Dart}
-- given
  (hIC : InterfaceConnected (offSupportComponent Vc z))
  (he : IsBoundaryDart (offSupportComponent Vc z) e)
  (hheads : ∀ d : Dart, (hd : IsBoundaryDart (offSupportComponent Vc z) d) → ((hypercubicLattice 2).induce (offSupportComponent Vc z)ᶜ).Reachable ⟨e.head, he.2⟩ ⟨d.head, hd.2⟩) :
-- imply
  {d : Dart | IsBoundaryDart (offSupportComponent Vc z) d} = {d : Dart | SameOrbit (offSupportComponent Vc z) e d} := by
-- proof
  apply StatMech.Lattice.fsv_canonicalMember_eq_orbit_of_residues Vc hIC he hheads

/--
[fsv_RegionSingleFace_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_RegionSingleFace_singleton_eq
  {c : Site 2} :
-- imply
  fsv_RegionSingleFace ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.fsv_RegionSingleFace_singleton c

/--
[fsv_canonical_eq_singleOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_canonical_eq_singleOrbit_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
-- imply
  fsv_canonicalFamily Vc = fsv_singleOrbitFamily Vc := by
-- proof
  apply StatMech.Lattice.fsv_canonical_eq_singleOrbit Vc hres

/--
[fsv_facialOrbitsCoverComponents_singleOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_facialOrbitsCoverComponents_singleOrbit_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
-- imply
  rsf_FacialOrbitsCoverComponents Vc (fsv_singleOrbitFamily Vc) := by
-- proof
  apply StatMech.Lattice.fsv_facialOrbitsCoverComponents_singleOrbit Vc hres

/--
[fsv_componentCount_eq_singleOrbitCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FacialSurjectivity.lean)
-/
@[path]
private lemma fsv_componentCount_eq_singleOrbitCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hres : ∀ z : Site 2, z ∉ Vc.support → fsv_RegionSingleFace (offSupportComponent Vc z)) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = Nat.card (fsv_singleOrbitFamily Vc) := by
-- proof
  apply StatMech.Lattice.fsv_componentCount_eq_singleOrbitCount Vc hres


-- created on 2026-10-23
