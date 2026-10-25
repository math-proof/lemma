import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
open Set SimpleGraph StatMech StatMech.Lattice


/--
[pww_farLeft_notMem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean)
-/
@[path]
private lemma pww_farLeft_notMem_leftRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {q : Site 2}
-- given
  (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0) :
-- imply
  q ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.pww_farLeft_notMem_leftRegion Vc hq

/--
[pww_oddRay_iff_oddCross_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean)
-/
@[path]
private lemma pww_oddRay_iff_oddCross_leftRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {q : Site 2}
  {γ : (hypercubicLattice 2).Walk (origin 2) q}
-- given
  (hq : ∀ p ∈ Vc.support, q 0 ≤ p 0) :
-- imply
  (¬ Even (jec_rayCount (origin 2) Vc)) ↔ (¬ Even (crossCount (jec_leftRegion Vc) γ)) := by
-- proof
  apply StatMech.Lattice.pww_oddRay_iff_oddCross_leftRegion Vc hq γ

/--
[pww_crossCount_eq_of_bdEdge_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean)
-/
@[path]
private lemma pww_crossCount_eq_of_bdEdge_match_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S T : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e) :
-- imply
  crossCount S w = crossCount T w := by
-- proof
  apply StatMech.Lattice.pww_crossCount_eq_of_bdEdge_match S T hbd w

/--
[pww_oddRay_of_bdEdge_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean)
-/
@[path]
private lemma pww_oddRay_of_bdEdge_match_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {q : Site 2}
  {γ : (hypercubicLattice 2).Walk (origin 2) q}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2)) Vc)
  (hqK : q ∉ cluster 2 ω (origin 2))
  (hqfar : ∀ p ∈ Vc.support, q 0 ≤ p 0) :
-- imply
  ¬ Even (jec_rayCount (origin 2) Vc) := by
-- proof
  apply StatMech.Lattice.pww_oddRay_of_bdEdge_match hfin Vc hmatch hqK hqfar γ

/--
[pww_origin_rayCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean)
-/
@[path]
private lemma pww_origin_rayCount_odd_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart}
  {q : Site 2}
  {γ : (hypercubicLattice 2).Walk (origin 2) q}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
  (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2)) (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
  (hqK : q ∉ cluster 2 ω (origin 2))
  (hqfar : ∀ p ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, q 0 ≤ p 0) :
-- imply
  ¬ Even (jec_rayCount (origin 2) (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he)) := by
-- proof
  apply StatMech.Lattice.pww_origin_rayCount_odd hfin e he hmatch hqK hqfar γ

/--
[pww_orbitIsLoop_of_bdEdge_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingWitness.lean)
-/
@[path]
private lemma pww_orbitIsLoop_of_bdEdge_match_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart}
  {q : Site 2}
  {γ : (hypercubicLattice 2).Walk (origin 2) q}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
  (ho : origin 2 ∈ cluster 2 ω (origin 2))
  (hExt : ∀ z, z ∉ cluster 2 ω (origin 2) → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support) ∧ (∀ qq ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, z0 0 ≤ qq 0))
  (hInt : ∀ z, z ∈ cluster 2 ω (origin 2) → ∃ p : (hypercubicLattice 2).Walk z (origin 2), (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support))
  (hmatch : pww_BdEdgeMatch (cluster 2 ω (origin 2)) (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
  (hqK : q ∉ cluster 2 ω (origin 2))
  (hqfar : ∀ p ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, q 0 ≤ p 0) :
-- imply
  ccs_OrbitIsLoop (cluster 2 ω (origin 2)) := by
-- proof
  apply StatMech.Lattice.pww_orbitIsLoop_of_bdEdge_match hfin e he ho hExt hInt hmatch hqK hqfar γ


-- created on 2026-10-23
