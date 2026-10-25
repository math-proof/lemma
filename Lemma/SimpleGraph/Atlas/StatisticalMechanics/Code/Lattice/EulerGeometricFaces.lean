import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[egf_loop_barrier_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_loop_barrier_on_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbar : ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Adj u v) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.egf_loop_barrier_on_support Vc hadj hbar

/--
[egf_leftRegion_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_leftRegion_sameSide_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (h : (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) :
-- imply
  (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.egf_leftRegion_sameSide Vc h

/--
[egf_rayCount_zero_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_rayCount_zero_above_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
  {R : ℤ}
-- given
  (hsupp : ∀ p ∈ w.support, p 1 ≤ R)
  (hz : R + 1 ≤ z 1) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.egf_rayCount_zero_above z w R hsupp hz

/--
[egf_rayCount_zero_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_rayCount_zero_below_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
  {R : ℤ}
-- given
  (hsupp : ∀ p ∈ w.support, -R ≤ p 1)
  (hz : z 1 ≤ -R) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.egf_rayCount_zero_below z w R hsupp hz

/--
[egf_ray_even_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_ray_even_exterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Lattice.egf_ray_even_exterior Vc R hsupp hz

/--
[egf_exterior_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_exterior_outside_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.egf_exterior_outside Vc R hsupp hz

/--
[egf_leftRegion_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_leftRegion_subset_box_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  jec_leftRegion Vc ⊆ box 2 R := by
-- proof
  apply StatMech.Lattice.egf_leftRegion_subset_box Vc R hsupp

/--
[egf_leftRegion_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_leftRegion_finite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  (jec_leftRegion Vc).Finite := by
-- proof
  apply StatMech.Lattice.egf_leftRegion_finite Vc R hsupp

/--
[egf_exterior_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_exterior_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.egf_exterior_reachable Vc R hsupp hx hy

/--
[egf_outsideComponent_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_outsideComponent_infinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  ((latticeMinusBarrier (jec_leftRegion Vc)).connectedComponentMk (beacon 2 R)).supp.Infinite := by
-- proof
  apply StatMech.Lattice.egf_outsideComponent_infinite Vc R hsupp

/--
[egf_loop_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_loop_two_components_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : egf_LoopFloodFill Vc) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.egf_loop_two_components Vc h

/--
[egf_cycle_faceCount_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_cycle_faceCount_eq_two_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  faceCount c.toSubgraph.coe = 2 := by
-- proof
  apply StatMech.Lattice.egf_cycle_faceCount_eq_two c hc

/--
[egf_cycle_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_cycle_two_components_eq
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hc : c.IsCycle)
  (h : egf_LoopFloodFill Vc) :
-- imply
  faceCount c.toSubgraph.coe = 2 ∧ Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.egf_cycle_two_components c hc Vc h

/--
[egf_face_eq_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_face_eq_geometric_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P) :
-- imply
  faceCount P.G = geometricRegionCount P + 1 := by
-- proof
  apply StatMech.Lattice.egf_face_eq_geometric P hJ

/--
[egf_geometricRegionCount_eq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_geometricRegionCount_eq_nullity_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P) :
-- imply
  geometricRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.egf_geometricRegionCount_eq_nullity P hJ

/--
[egf_euler_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean)
-/
@[path]
private lemma egf_euler_geometric_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P) :
-- imply
  (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1) = 1 + Nat.card P.G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.egf_euler_geometric P hJ


-- created on 2026-10-23
