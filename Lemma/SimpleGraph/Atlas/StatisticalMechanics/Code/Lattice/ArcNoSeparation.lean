import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
open Set SimpleGraph StatMech StatMech.Lattice


/--
[arcns_walk_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_walk_of_connected_eq
  {B : Set (Site 2)}
  {x y : Site 2}
-- given
  (h : arcns_OffSupportConnected B)
  (hx : x ∉ B)
  (hy : y ∉ B) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ B := by
-- proof
  apply StatMech.Lattice.arcns_walk_of_connected h hx hy

/--
[arcns_farLeft_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_farLeft_connected_eq
  {B : Set (Site 2)}
  {b : ℤ}
  {z1 z2 : Site 2}
-- given
  (hb : ∀ q ∈ B, b ≤ q 0)
  (h0 : z1 0 ≤ b - 1)
  (h1 : z2 0 ≤ b - 1) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk z1 z2, ∀ w ∈ p.support, w ∉ B := by
-- proof
  apply StatMech.Lattice.arcns_farLeft_connected B b hb z1 z2 h0 h1

/--
[arcns_connected_of_reachesFarLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_connected_of_reachesFarLeft_eq
  {B : Set (Site 2)}
-- given
  (h : arcns_ReachesFarLeft B) :
-- imply
  arcns_OffSupportConnected B := by
-- proof
  apply StatMech.Lattice.arcns_connected_of_reachesFarLeft h

/--
[arcns_vlshape_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_vlshape_support_eq
  {x0 y0 x1 y1 : ℤ}
  {z : Site 2} :
-- imply
  z ∈ (arcns_vlshape x0 y0 x1 y1).support ↔ (∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x0, t]) ∨ (∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y1]) := by
-- proof
  apply StatMech.Lattice.arcns_vlshape_support x0 y0 x1 y1 z

/--
[arcns_reachesFarLeft_singlePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_reachesFarLeft_singlePoint_eq
  {u : Site 2} :
-- imply
  arcns_ReachesFarLeft ({u} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.arcns_reachesFarLeft_singlePoint u

/--
[arcns_singlePoint_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_singlePoint_connected_eq
  {u : Site 2} :
-- imply
  arcns_OffSupportConnected ({u} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.arcns_singlePoint_connected u

/--
[arcns_connected_insert_of_leafRemovable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_connected_insert_of_leafRemovable_eq
  {S : Set (Site 2)}
  {u' : Site 2}
-- given
  (hres : arcns_LeafRemovable S u')
  (hS : arcns_OffSupportConnected S) :
-- imply
  arcns_OffSupportConnected (insert u' S) := by
-- proof
  apply StatMech.Lattice.arcns_connected_insert_of_leafRemovable hres hS

/--
[arcns_cons_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_cons_support_eq
  {u v w : Site 2}
  {q : (hypercubicLattice 2).Walk v w}
-- given
  (h : (hypercubicLattice 2).Adj u v) :
-- imply
  {z : Site 2 | z ∈ (Walk.cons h q).support} = insert u {z : Site 2 | z ∈ q.support} := by
-- proof
  apply StatMech.Lattice.arcns_cons_support h q

/--
[arcns_arc_no_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_arc_no_separation_eq
  {u w : Site 2}
  {p : (hypercubicLattice 2).Walk u w}
-- given
  (hp : p.IsPath)
  (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b) (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath → arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a) :
-- imply
  arcns_OffSupportConnected {z : Site 2 | z ∈ p.support} := by
-- proof
  apply StatMech.Lattice.arcns_arc_no_separation p hp hleaf

/--
[arcns_offSupport_reachable_of_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_offSupport_reachable_of_arc_eq
  {u w : Site 2}
  {p : (hypercubicLattice 2).Walk u w}
  {x y : Site 2}
-- given
  (hp : p.IsPath)
  (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b) (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath → arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a)
  (hx : x ∉ {z : Site 2 | z ∈ p.support})
  (hy : y ∉ {z : Site 2 | z ∈ p.support}) :
-- imply
  (ffc_offSupportLattice {z : Site 2 | z ∈ p.support}).Reachable x y := by
-- proof
  apply StatMech.Lattice.arcns_offSupport_reachable_of_arc p hp hleaf hx hy

/--
[arcns_floodFill_eq_offSupport_of_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_floodFill_eq_offSupport_of_arc_eq
  {u w : Site 2}
  {p : (hypercubicLattice 2).Walk u w}
  {seed : Site 2}
-- given
  (hp : p.IsPath)
  (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b) (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath → arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a)
  (hseed : seed ∉ {z : Site 2 | z ∈ p.support}) :
-- imply
  ffc_floodFill {z : Site 2 | z ∈ p.support} seed = {z : Site 2 | z ∉ {z : Site 2 | z ∈ p.support}} := by
-- proof
  apply StatMech.Lattice.arcns_floodFill_eq_offSupport_of_arc p hp hleaf hseed

/--
[arcns_singlePoint_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_singlePoint_nonvacuous_eq :
-- imply
  (ffc_offSupportLattice ({![0, 0]} : Set (Site 2))).Reachable ![1, 0] ![0, 1] := by
-- proof
  apply StatMech.Lattice.arcns_singlePoint_nonvacuous

/--
[arcns_leafRemovable_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean)
-/
@[path]
private lemma arcns_leafRemovable_empty_eq
  {u : Site 2} :
-- imply
  arcns_LeafRemovable (∅ : Set (Site 2)) u := by
-- proof
  apply StatMech.Lattice.arcns_leafRemovable_empty u


-- created on 2026-10-23
