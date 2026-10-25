import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[rsf_boundaryDart_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_boundaryDart_tail_mem_eq
  {C : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart C e) :
-- imply
  e.tail ∈ C := by
-- proof
  apply StatMech.Lattice.rsf_boundaryDart_tail_mem C he

/--
[rsf_boundaryDart_head_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_boundaryDart_head_not_mem_eq
  {C : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart C e) :
-- imply
  e.head ∉ C := by
-- proof
  apply StatMech.Lattice.rsf_boundaryDart_head_not_mem C he

/--
[rsf_no_shared_boundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_no_shared_boundaryDart_eq
  {C C' : Set (Site 2)}
  {e : Dart}
-- given
  (hCC' : Disjoint C C')
  (he : IsBoundaryDart C e)
  (he' : IsBoundaryDart C' e) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.rsf_no_shared_boundaryDart hCC' he he'

/--
[rsf_disjoint_boundaryDarts_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_disjoint_boundaryDarts_of_disjoint_eq
  {C C' : Set (Site 2)}
-- given
  (hCC' : Disjoint C C') :
-- imply
  Disjoint {e : Dart | IsBoundaryDart C e} {e : Dart | IsBoundaryDart C' e} := by
-- proof
  apply StatMech.Lattice.rsf_disjoint_boundaryDarts_of_disjoint hCC'

/--
[rsf_orbit_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_orbit_isBoundaryDart_eq
  {C : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart C e) :
-- imply
  IsBoundaryDart C ((dartNext C)^[k] e) := by
-- proof
  apply StatMech.Lattice.rsf_orbit_isBoundaryDart C he k

/--
[rsf_orbit_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_orbit_tail_mem_eq
  {C : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart C e) :
-- imply
  ((dartNext C)^[k] e).tail ∈ C := by
-- proof
  apply StatMech.Lattice.rsf_orbit_tail_mem C he k

/--
[rsf_orbit_head_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_orbit_head_not_mem_eq
  {C : Set (Site 2)}
  {e : Dart}
  {k : ℕ}
-- given
  (he : IsBoundaryDart C e) :
-- imply
  ((dartNext C)^[k] e).head ∉ C := by
-- proof
  apply StatMech.Lattice.rsf_orbit_head_not_mem C he k

/--
[rsf_facialOrbit_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_facialOrbit_next_eq
  {C : Set (Site 2)}
  {e : {d : Dart // IsBoundaryDart C d}} :
-- imply
  rsf_facialOrbit C (dartNextSub C e) = rsf_facialOrbit C e := by
-- proof
  apply StatMech.Lattice.rsf_facialOrbit_next C e

/--
[rsf_offSupportComponent_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_offSupportComponent_eq_of_mem_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed z : Site 2}
-- given
  (hz : z ∈ offSupportComponent Vc seed) :
-- imply
  offSupportComponent Vc z = offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.rsf_offSupportComponent_eq_of_mem Vc hz

/--
[rsf_offSupportComponent_eq_or_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_offSupportComponent_eq_or_disjoint_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s t : Site 2} :
-- imply
  offSupportComponent Vc s = offSupportComponent Vc t ∨ Disjoint (offSupportComponent Vc s) (offSupportComponent Vc t) := by
-- proof
  apply StatMech.Lattice.rsf_offSupportComponent_eq_or_disjoint Vc s t

/--
[rsf_componentBoundaryDart_determines_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_componentBoundaryDart_determines_component_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart (offSupportComponent Vc seed) e) :
-- imply
  offSupportComponent Vc e.tail = offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.rsf_componentBoundaryDart_determines_component Vc he

/--
[rsf_disjoint_boundaryDarts_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_disjoint_boundaryDarts_of_ne_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s t : Site 2}
-- given
  (hne : offSupportComponent Vc s ≠ offSupportComponent Vc t) :
-- imply
  Disjoint {e : Dart | IsBoundaryDart (offSupportComponent Vc s) e} {e : Dart | IsBoundaryDart (offSupportComponent Vc t) e} := by
-- proof
  apply StatMech.Lattice.rsf_disjoint_boundaryDarts_of_ne Vc hne

/--
[rsf_boundaryDart_unique_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_boundaryDart_unique_component_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s t : Site 2}
  {e : Dart}
-- given
  (hs : IsBoundaryDart (offSupportComponent Vc s) e)
  (ht : IsBoundaryDart (offSupportComponent Vc t) e) :
-- imply
  offSupportComponent Vc s = offSupportComponent Vc t := by
-- proof
  apply StatMech.Lattice.rsf_boundaryDart_unique_component Vc hs ht

/--
[rsf_reach_axis_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_reach_axis_le_eq
  {x : Site 2}
  {j : Fin 2}
  {a : ℤ}
  {n : ℕ} :
-- imply
  (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j (a + n)) := by
-- proof
  apply StatMech.Lattice.rsf_reach_axis_le x j a n

/--
[rsf_reach_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_reach_axis_eq
  {x : Site 2}
  {j : Fin 2}
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j b) := by
-- proof
  apply StatMech.Lattice.rsf_reach_axis x j a b

/--
[rsf_reach_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_reach_all_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Reachable x y := by
-- proof
  apply StatMech.Lattice.rsf_reach_all x y

/--
[rsf_walk_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_walk_crosses_eq
  {C : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ C)
  (hy : y ∉ C) :
-- imply
  ∃ e : Dart, IsBoundaryDart C e := by
-- proof
  apply StatMech.Lattice.rsf_walk_crosses C w hx hy

/--
[rsf_exists_boundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_exists_boundaryDart_eq
  {C : Set (Site 2)}
  {c z : Site 2}
-- given
  (hc : c ∈ C)
  (hz : z ∉ C) :
-- imply
  ∃ e : Dart, IsBoundaryDart C e := by
-- proof
  apply StatMech.Lattice.rsf_exists_boundaryDart C hc hz

/--
[rsf_offSupportComponent_exists_boundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_offSupportComponent_exists_boundaryDart_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ Vc.support) :
-- imply
  ∃ e : Dart, IsBoundaryDart (offSupportComponent Vc seed) e := by
-- proof
  apply StatMech.Lattice.rsf_offSupportComponent_exists_boundaryDart Vc hseed

/--
[rsf_fcb_reachable_offSupportComponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_fcb_reachable_offSupportComponent_eq_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}}
-- given
  (h : (fcb_offComplGraph Vc).Reachable x y) :
-- imply
  offSupportComponent Vc (x : Site 2) = offSupportComponent Vc (y : Site 2) := by
-- proof
  apply StatMech.Lattice.rsf_fcb_reachable_offSupportComponent_eq Vc h

/--
[rsf_fcb_reachable_of_offSupportComponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_fcb_reachable_of_offSupportComponent_eq_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : {z : Site 2 // z ∉ Vc.support}}
-- given
  (heq : offSupportComponent Vc (u : Site 2) = offSupportComponent Vc (v : Site 2)) :
-- imply
  (fcb_offComplGraph Vc).Reachable u v := by
-- proof
  apply StatMech.Lattice.rsf_fcb_reachable_of_offSupportComponent_eq Vc heq

/--
[rsf_componentDarts_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_componentDarts_mk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (v : {z : Site 2 // z ∉ Vc.support}) :
-- imply
  rsf_componentDarts Vc ((fcb_offComplGraph Vc).connectedComponentMk v) = {e : Dart | IsBoundaryDart (offSupportComponent Vc (v : Site 2)) e} := by
-- proof
  apply StatMech.Lattice.rsf_componentDarts_mk Vc v

/--
[rsf_componentDarts_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_componentDarts_injective_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Function.Injective (rsf_componentDarts Vc) := by
-- proof
  apply StatMech.Lattice.rsf_componentDarts_injective Vc

/--
[rsf_componentCount_le_facialOrbitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_componentCount_le_facialOrbitRange_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = Nat.card (Set.range (rsf_componentDarts Vc)) := by
-- proof
  apply StatMech.Lattice.rsf_componentCount_le_facialOrbitRange Vc

/--
[rsf_componentCount_eq_facialOrbitCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_componentCount_eq_facialOrbitCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {𝓕 : Set (Set Dart)}
-- given
  (hcov : rsf_FacialOrbitsCoverComponents Vc 𝓕) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = Nat.card 𝓕 := by
-- proof
  apply StatMech.Lattice.rsf_componentCount_eq_facialOrbitCount Vc hcov

/--
[rsf_componentDarts_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_componentDarts_nonempty_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c : (fcb_offComplGraph Vc).ConnectedComponent} :
-- imply
  (rsf_componentDarts Vc c).Nonempty := by
-- proof
  apply StatMech.Lattice.rsf_componentDarts_nonempty Vc c

/--
[rsf_facialOrbitRange_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RotationSystemFaces.lean)
-/
@[path]
private lemma rsf_facialOrbitRange_nonempty_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∉ Vc.support) :
-- imply
  (Set.range (rsf_componentDarts Vc)).Nonempty := by
-- proof
  apply StatMech.Lattice.rsf_facialOrbitRange_nonempty Vc hz


-- created on 2026-10-23
