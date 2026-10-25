import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.PivotalFactorComplete
open MeasureTheory Function Set SimpleGraph StatMech StatMech.Percolation


/--
[internal_edge_ne_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorComplete.lean)
-/
@[path]
private lemma internal_edge_ne_boundary_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
  {e : Sym2 (Site d)}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S)
  (he : e ∈ Sharpness.internalEdges (S : Set (Site d))) :
-- imply
  e ≠ s(x, y) := by
-- proof
  apply StatMech.Percolation.internal_edge_ne_boundary hx hy he

/--
[pivotal_of_surface_imp_withinConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorComplete.lean)
-/
@[path]
private lemma pivotal_of_surface_imp_withinConn_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (hS : surfaceSet d n ω = S)
  (h0S : origin d ∈ S)
  (hadj : (hypercubicLattice d).Adj x y)
  (hxS : x ∈ S)
  (hybox : y ∈ box d n)
  (hyS : y ∉ S)
  (hpiv : IsPivotal (s(x, y) : Sym2 (Site d)) (boxCrossingEvent d n) ω) :
-- imply
  ω ∈ withinConnEvent d (S : Set (Site d)) (origin d) x := by
-- proof
  apply StatMech.Percolation.pivotal_of_surface_imp_withinConn hS h0S hadj hxS hybox hyS hpiv

/--
[pivotal_surface_event_eq_withinConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorComplete.lean)
-/
@[path]
private lemma pivotal_surface_event_eq_withinConn_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (h0S : origin d ∈ S)
  (hSinner : (S : Set (Site d)) ⊆ box d (n - 1))
  (hn : 1 ≤ n)
  (he : e ∈ boundaryEdges d S) :
-- imply
  pivotalEvent s(e.1, e.2) (boxCrossingEvent d n) ∩ surfaceEvent d n S = withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ surfaceEvent d n S := by
-- proof
  apply StatMech.Percolation.pivotal_surface_event_eq_withinConn h0S hSinner hn he

/--
[pivotal_surface_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorComplete.lean)
-/
@[path]
private lemma pivotal_surface_factor_eq
  {d : ℕ}
  {n : ℕ}
  {S : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0S : origin d ∈ S)
  (hSinner : (S : Set (Site d)) ⊆ box d (n - 1))
  (hn : 1 ≤ n)
  (he : e ∈ boundaryEdges d S) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (pivotalEvent s(e.1, e.2) (boxCrossingEvent d n) ∩ surfaceEvent d n S) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) e.1) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) := by
-- proof
  apply StatMech.Percolation.pivotal_surface_factor p hp h0S hSinner hn he


-- created on 2026-10-23
