import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.CrossingParity
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[crossCount_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_nil_eq
  {S : Set (Site 2)}
  {x : Site 2} :
-- imply
  crossCount S (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
-- proof
  apply StatMech.Lattice.crossCount_nil S x

/--
[crossCount_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_cons_eq
  {S : Set (Site 2)}
  {a b c : Site 2}
  {p : (hypercubicLattice 2).Walk b c}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  crossCount S (Walk.cons hab p) = (if bdEdge S s(a, b) then 1 else 0) + crossCount S p := by
-- proof
  apply StatMech.Lattice.crossCount_cons S hab p

/--
[crossCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_append_eq
  {S : Set (Site 2)}
  {x y z : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
  {q : (hypercubicLattice 2).Walk y z} :
-- imply
  crossCount S (p.append q) = crossCount S p + crossCount S q := by
-- proof
  apply StatMech.Lattice.crossCount_append S p q

/--
[crossCount_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_reverse_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  crossCount S w.reverse = crossCount S w := by
-- proof
  apply StatMech.Lattice.crossCount_reverse S w

/--
[crossCount_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_parity_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Lattice.crossCount_parity S w

/--
[crossCount_parity_eq_of_sameEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_parity_eq_of_sameEndpoints_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w₁ w₂ : (hypercubicLattice 2).Walk x y} :
-- imply
  crossCount S w₁ % 2 = crossCount S w₂ % 2 := by
-- proof
  apply StatMech.Lattice.crossCount_parity_eq_of_sameEndpoints S w₁ w₂

/--
[face_flip_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma face_flip_parity_eq
  {S : Set (Site 2)}
  {a b : ℤ}
  {w₁ w₂ : (hypercubicLattice 2).Walk (faceCorner00 a b) (faceCorner11 a b)} :
-- imply
  crossCount S w₁ % 2 = crossCount S w₂ % 2 := by
-- proof
  apply StatMech.Lattice.face_flip_parity S a b w₁ w₂

/--
[crossCount_even_of_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_even_of_loop_eq
  {S : Set (Site 2)}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (crossCount S w) := by
-- proof
  apply StatMech.Lattice.crossCount_even_of_loop S w

/--
[crossCount_odd_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma crossCount_odd_of_separated_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ Even (crossCount S w) := by
-- proof
  apply StatMech.Lattice.crossCount_odd_of_separated S hx hy w

/--
[latticeMinusBarrier_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma latticeMinusBarrier_adj_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  (latticeMinusBarrier S).Adj x y ↔ (hypercubicLattice 2).Adj x y ∧ ¬ bdEdge S s(x, y) := by
-- proof
  apply StatMech.Lattice.latticeMinusBarrier_adj S x y

/--
[latticeMinusBarrier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma latticeMinusBarrier_le_eq
  {S : Set (Site 2)} :
-- imply
  latticeMinusBarrier S ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.latticeMinusBarrier_le S

/--
[latticeMinusBarrier_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma latticeMinusBarrier_sameSide_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (latticeMinusBarrier S).Walk x y} :
-- imply
  (x ∈ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Lattice.latticeMinusBarrier_sameSide S w

/--
[not_reachable_latticeMinusBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma not_reachable_latticeMinusBarrier_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ (latticeMinusBarrier S).Reachable x y := by
-- proof
  apply StatMech.Lattice.not_reachable_latticeMinusBarrier S hx hy

/--
[faceBoundaryGraph_sharedPrimalEdge_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma faceBoundaryGraph_sharedPrimalEdge_bdEdge_eq
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (h : (faceBoundaryGraph S).Adj f g) :
-- imply
  bdEdge S (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.faceBoundaryGraph_sharedPrimalEdge_bdEdge S h

/--
[sharedPrimalEdge_isLatticeEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma sharedPrimalEdge_isLatticeEdge_eq
  {f g : Site 2}
-- given
  (_h : (hypercubicLattice 2).Adj f g) :
-- imply
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_isLatticeEdge _h

/--
[faceBoundaryWalk_edges_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma faceBoundaryWalk_edges_bdEdge_eq
  {S : Set (Site 2)}
  {u v : Site 2}
  {c : (faceBoundaryGraph S).Walk u v}
  {f g : Site 2}
-- given
  (h : s(f, g) ∈ c.edges) :
-- imply
  bdEdge S (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.faceBoundaryWalk_edges_bdEdge S c h

/--
[cluster_separated_from_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma cluster_separated_from_exterior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
-- given
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z := by
-- proof
  apply StatMech.Lattice.cluster_separated_from_exterior o hz

/--
[origin_crossCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma origin_crossCount_odd_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk o z}
-- given
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ¬ Even (crossCount (cluster 2 ω o) w) := by
-- proof
  apply StatMech.Lattice.origin_crossCount_odd o hz w

/--
[cluster_enclosed_by_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma cluster_enclosed_by_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk o z}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hz : z ∉ cluster 2 ω o) :
-- imply
  (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) ∧ ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z := by
-- proof
  apply StatMech.Lattice.cluster_enclosed_by_dualCircuit o hfin w hz

/--
[cluster_enclosed_with_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean)
-/
@[path]
private lemma cluster_enclosed_with_winding_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk o z}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hz : z ∉ cluster 2 ω o) :
-- imply
  (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) ∧ ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z ∧ ∀ γ : (hypercubicLattice 2).Walk o z, ¬ Even (crossCount (cluster 2 ω o) γ) := by
-- proof
  apply StatMech.Lattice.cluster_enclosed_with_winding o hfin w hz


-- created on 2026-10-23
